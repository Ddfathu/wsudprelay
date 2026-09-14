#!/usr/bin/env node
'use strict';
const net = require('node:net');
const dgram = require('node:dgram');
const dns = require('node:dns').promises;
const http = require('node:http');
const { createHash } = require('node:crypto');
const { EventEmitter } = require('node:events');

const CONFIG = Object.freeze({
    LISTEN_HOST: '0.0.0.0',
    LISTEN_PORT: parseInt(process.env.PORT, 10) || 8080,
    // WebSocket endpoint. Set to '' to accept every path.
    WS_PATH: '/',
    MAX_WS_MESSAGE_BYTES: 4 * 1024 * 1024,
    HANDSHAKE_TIMEOUT_MS: 10000,
    IDLE_TIMEOUT_MS: 300000,
    XUDP_GRACE_MS: 60000,
    MAX_CONNECTIONS: 4096,
    // Diubah ke false agar port UDP 443 (QUIC / STUN) tidak ditolak
    REJECT_UDP_443: false,
});

const RELAY_MAGIC = Buffer.from('VLRLY004', 'ascii');
const RELAY_MODE_FIXED_UDP = 0x01;
const RELAY_MODE_MUX = 0x02;
const RELAY_MODE_PACKET_UDP = 0x03;
const ATYP_IPV4 = 0x01;
const ATYP_DOMAIN = 0x02;
const ATYP_IPV6 = 0x03;
const MUX_STATUS_NEW = 0x01;
const MUX_STATUS_KEEP = 0x02;
const MUX_STATUS_END = 0x03;
const MUX_STATUS_KEEPALIVE = 0x04;
const MUX_OPTION_DATA = 0x01;
const MUX_OPTION_ERROR = 0x02;
const MUX_NETWORK_UDP = 0x02;
const MAX_MUX_META_LEN = 512;
const MAX_PACKET_LEN = 65535;
const utf8Fatal = new TextDecoder('utf-8', { fatal: true });

function rejectUdpTarget(_target) {
    return false;
}

function buildConfig(overrides = {}) {
    const cfg = {
        listenAddress: { host: CONFIG.LISTEN_HOST, port: CONFIG.LISTEN_PORT },
        handshakeTimeout: CONFIG.HANDSHAKE_TIMEOUT_MS,
        idleTimeout: CONFIG.IDLE_TIMEOUT_MS,
        xudpGrace: CONFIG.XUDP_GRACE_MS,
        maxConns: CONFIG.MAX_CONNECTIONS,
        wsPath: CONFIG.WS_PATH,
        maxWsMessageBytes: CONFIG.MAX_WS_MESSAGE_BYTES,
        ...overrides,
    };
    if (!cfg.listenAddress || !Number.isInteger(cfg.listenAddress.port) || cfg.listenAddress.port < 0 || cfg.listenAddress.port > 65535) {
        throw new Error('invalid listen address');
    }
    if (!Number.isInteger(cfg.maxConns) || cfg.maxConns < 1) {
        throw new Error('MAX_CONNECTIONS must be >= 1');
    }
    if (!Number.isInteger(cfg.maxWsMessageBytes) || cfg.maxWsMessageBytes < 65536) {
        throw new Error('MAX_WS_MESSAGE_BYTES must be >= 65536');
    }
    return cfg;
}

class AsyncByteReader {
    constructor(socket) {
        this.socket = socket;
        this.buffers = [];
        this.available = 0;
        this.waiters = [];
        this.ended = false;
        this.error = null;
        socket.on('data', (chunk) => {
            if (!chunk || chunk.length === 0) {
                return;
            }
            this.buffers.push(Buffer.from(chunk));
            this.available += chunk.length;
            this._flush();
        });
        socket.on('end', () => {
            this.ended = true;
            this._flush();
        });
        socket.on('close', () => {
            this.ended = true;
            this._flush();
        });
        socket.on('error', (err) => {
            this.error = err;
            this._flush();
        });
    }
    readExactly(length) {
        if (!Number.isInteger(length) || length < 0) {
            return Promise.reject(new Error('invalid read length'));
        }
        if (length === 0) {
            return Promise.resolve(Buffer.alloc(0));
        }
        if (this.available >= length) {
            return Promise.resolve(this._take(length));
        }
        if (this.error) {
            return Promise.reject(this.error);
        }
        if (this.ended) {
            return Promise.reject(new Error('unexpected EOF'));
        }
        return new Promise((resolve, reject) => {
            this.waiters.push({ length, resolve, reject });
        });
    }
    _flush() {
        while (this.waiters.length > 0) {
            const waiter = this.waiters[0];
            if (this.available >= waiter.length) {
                this.waiters.shift();
                waiter.resolve(this._take(waiter.length));
                continue;
            }
            if (this.error || this.ended) {
                this.waiters.shift();
                waiter.reject(this.error || new Error('unexpected EOF'));
                continue;
            }
            break;
        }
    }
    _take(length) {
        const out = Buffer.allocUnsafe(length);
        let offset = 0;
        while (offset < length) {
            const first = this.buffers[0];
            const need = length - offset;
            if (first.length <= need) {
                first.copy(out, offset);
                offset += first.length;
                this.buffers.shift();
            }
            else {
                first.copy(out, offset, 0, need);
                this.buffers[0] = first.subarray(need);
                offset += need;
            }
        }
        this.available -= length;
        return out;
    }
}

async function readLengthPayload(reader) {
    const lenBuf = await reader.readExactly(2);
    const length = lenBuf.readUInt16BE(0);
    return length === 0 ? Buffer.alloc(0) : reader.readExactly(length);
}

async function readEndpoint(reader) {
    const head = await reader.readExactly(3);
    const port = head.readUInt16BE(0);
    const atyp = head[2];
    if (port === 0) {
        throw new Error('zero port');
    }
    return readEndpointBody(reader, atyp, port);
}

async function readEndpointBody(reader, atyp, port) {
    if (atyp === ATYP_IPV4) {
        const b = await reader.readExactly(4);
        return { host: `${b[0]}.${b[1]}.${b[2]}.${b[3]}`, port, atyp };
    }
    if (atyp === ATYP_DOMAIN) {
        const len = (await reader.readExactly(1))[0];
        if (len === 0) {
            throw new Error('empty domain');
        }
        const b = await reader.readExactly(len);
        let host;
        try {
            host = utf8Fatal.decode(b);
        }
        catch {
            throw new Error('invalid UTF-8 domain');
        }
        if (!host) {
            throw new Error('empty domain');
        }
        return { host, port, atyp };
    }
    if (atyp === ATYP_IPV6) {
        const b = await reader.readExactly(16);
        return { host: formatIPv6(b), port, atyp };
    }
    throw new Error(`unknown address type ${atyp}`);
}

function parseEndpointBytes(buffer, offset) {
    if (offset < 0 || buffer.length - offset < 3) {
        throw new Error('unexpected EOF in endpoint');
    }
    const port = buffer.readUInt16BE(offset);
    if (port === 0) {
        throw new Error('zero port');
    }
    const atyp = buffer[offset + 2];
    let cursor = offset + 3;
    if (atyp === ATYP_IPV4) {
        if (buffer.length - cursor < 4) {
            throw new Error('unexpected EOF in IPv4');
        }
        const b = buffer.subarray(cursor, cursor + 4);
        cursor += 4;
        return { endpoint: { host: `${b[0]}.${b[1]}.${b[2]}.${b[3]}`, port, atyp }, next: cursor };
    }
    if (atyp === ATYP_DOMAIN) {
        if (buffer.length - cursor < 1) {
            throw new Error('unexpected EOF in domain length');
        }
        const len = buffer[cursor++];
        if (len === 0 || buffer.length - cursor < len) {
            throw new Error('invalid domain length');
        }
        let host;
        try {
            host = utf8Fatal.decode(buffer.subarray(cursor, cursor + len));
        }
        catch {
            throw new Error('invalid UTF-8 domain');
        }
        cursor += len;
        return { endpoint: { host, port, atyp }, next: cursor };
    }
    if (atyp === ATYP_IPV6) {
        if (buffer.length - cursor < 16) {
            throw new Error('unexpected EOF in IPv6');
        }
        const host = formatIPv6(buffer.subarray(cursor, cursor + 16));
        cursor += 16;
        return { endpoint: { host, port, atyp }, next: cursor };
    }
    throw new Error(`unknown address type ${atyp}`);
}

function formatIPv6(bytes) {
    const parts = [];
    for (let i = 0; i < 16; i += 2) {
        parts.push(bytes.readUInt16BE(i).toString(16));
    }
    return parts.join(':');
}

function ipv6ToBytes(address) {
    let input = address;
    const zone = input.indexOf('%');
    if (zone >= 0) {
        input = input.slice(0, zone);
    }
    let ipv4Tail = null;
    const lastColon = input.lastIndexOf(':');
    if (input.includes('.') && lastColon >= 0) {
        const ipv4 = input.slice(lastColon + 1).split('.').map(Number);
        if (ipv4.length !== 4 || ipv4.some((n) => !Number.isInteger(n) || n < 0 || n > 255)) {
            throw new Error(`invalid IPv6 address: ${address}`);
        }
        ipv4Tail = [((ipv4[0] << 8) | ipv4[1]).toString(16), ((ipv4[2] << 8) | ipv4[3]).toString(16)];
        input = input.slice(0, lastColon) + ':' + ipv4Tail.join(':');
    }
    const halves = input.split('::');
    if (halves.length > 2) {
        throw new Error(`invalid IPv6 address: ${address}`);
    }
    const left = halves[0] ? halves[0].split(':').filter(Boolean) : [];
    const right = halves.length === 2 && halves[1] ? halves[1].split(':').filter(Boolean) : [];
    const missing = 8 - left.length - right.length;
    if ((halves.length === 1 && missing !== 0) || (halves.length === 2 && missing < 1)) {
        throw new Error(`invalid IPv6 address: ${address}`);
    }
    const words = [...left, ...Array(Math.max(0, missing)).fill('0'), ...right];
    if (words.length !== 8) {
        throw new Error(`invalid IPv6 address: ${address}`);
    }
    const out = Buffer.alloc(16);
    words.forEach((word, i) => {
        if (!/^[0-9a-f]{1,4}$/i.test(word)) {
            throw new Error(`invalid IPv6 address: ${address}`);
        }
        out.writeUInt16BE(parseInt(word, 16), i * 2);
    });
    return out;
}

function encodeUDPSource(rinfo) {
    const port = Number(rinfo.port);
    if (!Number.isInteger(port) || port < 1 || port > 65535) {
        throw new Error('invalid UDP source port');
    }
    const family = net.isIP(rinfo.address);
    const head = Buffer.alloc(3);
    head.writeUInt16BE(port, 0);
    if (family === 4) {
        head[2] = ATYP_IPV4;
        return Buffer.concat([head, Buffer.from(rinfo.address.split('.').map(Number))]);
    }
    if (family === 6) {
        head[2] = ATYP_IPV6;
        return Buffer.concat([head, ipv6ToBytes(rinfo.address)]);
    }
    throw new Error(`invalid UDP source IP: ${rinfo.address}`);
}

function writeSocket(socket, data) {
    if (socket.destroyed || !socket.writable) {
        return Promise.reject(new Error('socket is closed'));
    }
    return new Promise((resolve, reject) => {
        socket.write(data, (err) => err ? reject(err) : resolve());
    });
}

async function writeControlError(socket, message) {
    let body = Buffer.from(String(message || 'relay error'), 'utf8');
    if (body.length > MAX_PACKET_LEN) {
        body = body.subarray(0, MAX_PACKET_LEN);
    }
    const out = Buffer.allocUnsafe(3 + body.length);
    out[0] = 1;
    out.writeUInt16BE(body.length, 1);
    body.copy(out, 3);
    try {
        await writeSocket(socket, out);
    }
    catch { }
}

async function readControl(reader) {
    const magic = await reader.readExactly(RELAY_MAGIC.length);
    if (!magic.equals(RELAY_MAGIC)) {
        throw new Error('bad magic');
    }
    const mode = (await reader.readExactly(1))[0];
    if (![RELAY_MODE_FIXED_UDP, RELAY_MODE_MUX, RELAY_MODE_PACKET_UDP].includes(mode)) {
        throw new Error('bad mode');
    }
    const target = mode === RELAY_MODE_FIXED_UDP ? await readEndpoint(reader) : null;
    return { mode, target };
}

async function resolveTarget(target) {
    if (target.atyp === ATYP_IPV4) {
        return { address: target.host, family: 4 };
    }
    if (target.atyp === ATYP_IPV6) {
        return { address: target.host, family: 6 };
    }
    const records = await dns.lookup(target.host, { all: true, verbatim: true });
    if (!records.length) {
        throw new Error(`DNS returned no address for ${target.host}`);
    }
    const preferred = records.find((r) => r.family === 4) || records.find((r) => r.family === 6);
    if (!preferred) {
        throw new Error(`DNS returned unsupported address for ${target.host}`);
    }
    return preferred;
}

function bindDgram(socket, port, address) {
    return new Promise((resolve, reject) => {
        const onError = (err) => { cleanup(); reject(err); };
        const onListening = () => { cleanup(); resolve(); };
        const cleanup = () => {
            socket.off('error', onError);
            socket.off('listening', onListening);
        };
        socket.once('error', onError);
        socket.once('listening', onListening);
        socket.bind(port, address);
    });
}

class UDPAssociation {
    constructor() {
        this.udp4 = null;
        this.udp6 = null;
        this.port = 0;
        this.sink = null;
        this.closed = false;
    }
    static async create() {
        const assoc = new UDPAssociation();
        assoc.udp4 = dgram.createSocket({ type: 'udp4', reuseAddr: true });
        await bindDgram(assoc.udp4, 0, '0.0.0.0');
        assoc.port = assoc.udp4.address().port;
        assoc.udp4.on('message', (msg, rinfo) => assoc._onMessage(msg, rinfo));
        assoc.udp4.on('error', () => { });
        assoc.udp6 = dgram.createSocket({ type: 'udp6', reuseAddr: true, ipv6Only: true });
        try {
            await bindDgram(assoc.udp6, assoc.port, '::');
            assoc.udp6.on('message', (msg, rinfo) => assoc._onMessage(msg, rinfo));
            assoc.udp6.on('error', () => { });
        }
        catch {
            try {
                assoc.udp6.close();
            }
            catch { }
            assoc.udp6 = null;
        }
        return assoc;
    }
    attach(sink) {
        const old = this.sink;
        this.sink = sink;
        return old;
    }
    detach(mux, id) {
        if (this.sink && this.sink.mux === mux && this.sink.id === id) {
            this.sink = null;
            return true;
        }
        return false;
    }
    async send(target, payload) {
        if (this.closed) {
            throw new Error('UDP association is closed');
        }
        if (payload.length > MAX_PACKET_LEN) {
            throw new Error(`UDP payload too large: ${payload.length}`);
        }
        const resolved = await resolveTarget(target);
        const socket = resolved.family === 6 ? this.udp6 : this.udp4;
        if (!socket) {
            throw new Error(`UDP IPv${resolved.family} is unavailable on this host`);
        }
        await new Promise((resolve, reject) => {
            socket.send(payload, target.port, resolved.address, (err) => err ? reject(err) : resolve());
        });
    }
    _onMessage(msg, rinfo) {
        const sink = this.sink;
        if (!sink || this.closed) {
            return;
        }
        Promise.resolve(sink.mux.sendUDPData(sink.id, rinfo, Buffer.from(msg))).catch(() => { });
    }
    close() {
        if (this.closed) {
            return;
        }
        this.closed = true;
        this.sink = null;
        if (this.udp4) {
            try {
                this.udp4.close();
            }
            catch { }
        }
        if (this.udp6) {
            try {
                this.udp6.close();
            }
            catch { }
        }
        this.udp4 = null;
        this.udp6 = null;
    }
}

class XUDPManager {
    constructor(graceMs) {
        this.graceMs = graceMs;
        this.entries = new Map();
    }
    async attach(globalID, mux, sessionID) {
        const key = Buffer.from(globalID).toString('hex');
        let entry = this.entries.get(key);
        if (!entry) {
            entry = { assoc: await UDPAssociation.create(), timer: null };
            this.entries.set(key, entry);
        }
        if (entry.timer) {
            clearTimeout(entry.timer);
            entry.timer = null;
        }
        const oldSink = entry.assoc.attach({ mux, id: sessionID });
        return { assoc: entry.assoc, oldSink };
    }
    detach(globalID, mux, sessionID) {
        const key = Buffer.from(globalID).toString('hex');
        const entry = this.entries.get(key);
        if (!entry || !entry.assoc.detach(mux, sessionID)) {
            return;
        }
        if (entry.timer) {
            clearTimeout(entry.timer);
        }
        entry.timer = setTimeout(() => {
            const current = this.entries.get(key);
            if (current !== entry) {
                return;
            }
            this.entries.delete(key);
            entry.assoc.close();
        }, this.graceMs);
        entry.timer.unref?.();
    }
    close() {
        for (const entry of this.entries.values()) {
            if (entry.timer) {
                clearTimeout(entry.timer);
            }
            entry.assoc.close();
        }
        this.entries.clear();
    }
}

async function serveDirectUDP(socket, reader, target) {
    const assoc = await UDPAssociation.create();
    let closed = false;
    assoc.attach({
        mux: {
            sendUDPData: async (_id, _rinfo, data) => {
                if (closed || socket.destroyed) {
                    return;
                }
                if (data.length > MAX_PACKET_LEN) {
                    return;
                }
                const frame = Buffer.allocUnsafe(2 + data.length);
                frame.writeUInt16BE(data.length, 0);
                data.copy(frame, 2);
                await writeSocket(socket, frame);
            },
        },
        id: 0,
    });
    try {
        await writeSocket(socket, Buffer.from([0]));
        for (;;) {
            const payload = await readLengthPayload(reader);
            if (payload.length === 0) {
                continue;
            }
            await assoc.send(target, payload);
        }
    }
    finally {
        closed = true;
        assoc.close();
    }
}

async function servePacketUDP(socket, reader) {
    const assoc = await UDPAssociation.create();
    let closed = false;
    const writeChain = { value: Promise.resolve() };
    assoc.attach({
        mux: {
            sendUDPData: (_id, rinfo, data) => {
                if (closed || socket.destroyed || data.length > MAX_PACKET_LEN) {
                    return Promise.resolve();
                }
                const endpoint = encodeUDPSource(rinfo);
                const len = Buffer.allocUnsafe(2);
                len.writeUInt16BE(data.length, 0);
                const frame = Buffer.concat([endpoint, len, data]);
                const op = writeChain.value.then(() => writeSocket(socket, frame));
                writeChain.value = op.catch(() => { });
                return op;
            },
        },
        id: 0,
    });
    try {
        await writeSocket(socket, Buffer.from([0]));
        for (;;) {
            const target = await readEndpoint(reader);
            const payload = await readLengthPayload(reader);
            if (payload.length === 0) {
                continue;
            }
            await assoc.send(target, payload);
        }
    }
    finally {
        closed = true;
        assoc.close();
    }
}

async function readMuxFrame(reader) {
    const metaLen = (await reader.readExactly(2)).readUInt16BE(0);
    if (metaLen < 4 || metaLen > MAX_MUX_META_LEN) {
        throw new Error(`invalid mux metadata length ${metaLen}`);
    }
    const meta = await reader.readExactly(metaLen);
    const frame = {
        id: meta.readUInt16BE(0),
        status: meta[2],
        option: meta[3],
        network: 0,
        target: null,
        globalID: null,
        data: Buffer.alloc(0),
    };
    let cursor = 4;
    if (frame.status === MUX_STATUS_NEW) {
        if (cursor >= meta.length) {
            throw new Error('mux New missing network');
        }
        frame.network = meta[cursor++];
        const parsed = parseEndpointBytes(meta, cursor);
        frame.target = parsed.endpoint;
        cursor = parsed.next;
        if (frame.network === MUX_NETWORK_UDP && meta.length - cursor >= 8) {
            const gid = meta.subarray(cursor, cursor + 8);
            if (!gid.equals(Buffer.alloc(8))) {
                frame.globalID = Buffer.from(gid);
            }
            cursor += 8;
        }
        if (cursor !== meta.length) {
            throw new Error(`unexpected ${meta.length - cursor} byte(s) in mux New metadata`);
        }
    }
    else if (frame.status === MUX_STATUS_KEEP && meta.length > cursor && meta[cursor] === MUX_NETWORK_UDP) {
        frame.network = meta[cursor++];
        frame.target = parseEndpointBytes(meta, cursor).endpoint;
    }
    if ((frame.option & MUX_OPTION_DATA) !== 0) {
        frame.data = await readLengthPayload(reader);
    }
    return frame;
}

class MuxSession {
    constructor(mux, id, network, target) {
        this.mux = mux;
        this.id = id;
        this.network = network;
        this.target = target;
        this.udp = null;
        this.global = false;
        this.gid = null;
        this.closed = false;
    }
    async sendUDP(target, payload) {
        if (!this.udp) {
            throw new Error('UDP session is unavailable');
        }
        await this.udp.send(target, payload);
    }
    closeWithoutRemoving() {
        if (this.closed) {
            return;
        }
        this.closed = true;
        if (this.udp) {
            if (this.global) {
                this.mux.xm.detach(this.gid, this.mux, this.id);
            }
            else {
                this.udp.detach(this.mux, this.id);
                this.udp.close();
            }
            this.udp = null;
        }
    }
    async close(sendEnd) {
        if (this.mux.sessions.get(this.id) === this) {
            this.mux.sessions.delete(this.id);
        }
        this.closeWithoutRemoving();
        if (sendEnd) {
            await this.mux.sendEnd(this.id, true).catch(() => { });
        }
    }
}

class MuxConnection {
    constructor(socket, reader, cfg, xm) {
        this.socket = socket;
        this.reader = reader;
        this.cfg = cfg;
        this.xm = xm;
        this.sessions = new Map();
        this.closed = false;
        this.writeChain = Promise.resolve();
    }
    async serve() {
        try {
            await writeSocket(this.socket, Buffer.from([0]));
            for (;;) {
                const frame = await readMuxFrame(this.reader);
                await this.handleFrame(frame);
            }
        }
        finally {
            this.closeAll();
        }
    }
    async handleFrame(frame) {
        if (frame.status === MUX_STATUS_KEEPALIVE) {
            return;
        }
        if (frame.status === MUX_STATUS_NEW) {
            return this.handleNew(frame);
        }
        if (frame.status === MUX_STATUS_KEEP) {
            return this.handleKeep(frame);
        }
        if (frame.status === MUX_STATUS_END) {
            const session = this.sessions.get(frame.id);
            if (session && frame.data.length) {
                await session.sendUDP(session.target, frame.data).catch(() => { });
            }
            this.removeSession(frame.id);
            return;
        }
        throw new Error(`unknown mux status 0x${frame.status.toString(16).padStart(2, '0')}`);
    }
    async handleNew(frame) {
        if (frame.network !== MUX_NETWORK_UDP || !frame.target?.host || !frame.target?.port) {
            await this.sendEnd(frame.id, true).catch(() => { });
            return;
        }
        this.removeSession(frame.id);
        const session = new MuxSession(this, frame.id, frame.network, frame.target);
        if (frame.globalID) {
            try {
                const { assoc, oldSink } = await this.xm.attach(frame.globalID, this, frame.id);
                session.udp = assoc;
                session.global = true;
                session.gid = Buffer.from(frame.globalID);
                this.sessions.set(session.id, session);
                if (oldSink && (oldSink.mux !== this || oldSink.id !== frame.id)) {
                    oldSink.mux.removeSession(oldSink.id);
                    await oldSink.mux.sendEnd(oldSink.id, false).catch(() => { });
                }
            }
            catch {
                await this.sendEnd(frame.id, true).catch(() => { });
                return;
            }
        }
        else {
            try {
                const assoc = await UDPAssociation.create();
                assoc.attach({ mux: this, id: frame.id });
                session.udp = assoc;
                this.sessions.set(session.id, session);
            }
            catch {
                await this.sendEnd(frame.id, true).catch(() => { });
                return;
            }
        }
        if (frame.data.length) {
            await session.sendUDP(frame.target, frame.data).catch(() => session.close(true));
        }
    }
    async handleKeep(frame) {
        const session = this.sessions.get(frame.id);
        if (!session) {
            await this.sendEnd(frame.id, false).catch(() => { });
            return;
        }
        if (!frame.data.length) {
            return;
        }
        let target = session.target;
        if (frame.network === MUX_NETWORK_UDP && frame.target?.host && frame.target?.port) {
            target = frame.target;
            session.target = target;
        }
        await session.sendUDP(target, frame.data).catch(() => session.close(true));
    }
    removeSession(id) {
        const session = this.sessions.get(id);
        if (!session) {
            return;
        }
        this.sessions.delete(id);
        session.closeWithoutRemoving();
    }
    closeAll() {
        if (this.closed) {
            return;
        }
        this.closed = true;
        const sessions = [...this.sessions.values()];
        this.sessions.clear();
        for (const session of sessions) {
            session.closeWithoutRemoving();
        }
    }
    _queueWrite(data) {
        const op = this.writeChain.then(() => writeSocket(this.socket, data));
        this.writeChain = op.catch(() => { });
        return op;
    }
    sendUDPData(id, source, data) {
        const addr = encodeUDPSource(source);
        const meta = Buffer.allocUnsafe(5 + addr.length);
        meta.writeUInt16BE(id, 0);
        meta[2] = MUX_STATUS_KEEP;
        meta[3] = MUX_OPTION_DATA;
        meta[4] = MUX_NETWORK_UDP;
        addr.copy(meta, 5);
        return this.writeMuxPacket(meta, data);
    }
    sendEnd(id, hasError) {
        const meta = Buffer.alloc(4);
        meta.writeUInt16BE(id, 0);
        meta[2] = MUX_STATUS_END;
        meta[3] = hasError ? MUX_OPTION_ERROR : 0;
        return this.writeMuxMeta(meta);
    }
    writeMuxPacket(meta, data) {
        if (data.length > MAX_PACKET_LEN) {
            return Promise.reject(new Error(`mux payload too large: ${data.length}`));
        }
        const out = Buffer.allocUnsafe(2 + meta.length + 2 + data.length);
        out.writeUInt16BE(meta.length, 0);
        meta.copy(out, 2);
        const off = 2 + meta.length;
        out.writeUInt16BE(data.length, off);
        data.copy(out, off + 2);
        return this._queueWrite(out);
    }
    writeMuxMeta(meta) {
        const out = Buffer.allocUnsafe(2 + meta.length);
        out.writeUInt16BE(meta.length, 0);
        meta.copy(out, 2);
        return this._queueWrite(out);
    }
}

const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

function websocketAccept(key) {
    return createHash('sha1').update(String(key) + WS_GUID, 'ascii').digest('base64');
}

function websocketFrame(opcode, payload = Buffer.alloc(0)) {
    const body = Buffer.isBuffer(payload) ? payload : Buffer.from(payload);
    let header;
    if (body.length < 126) {
        header = Buffer.allocUnsafe(2);
        header[1] = body.length;
    }
    else if (body.length <= 0xffff) {
        header = Buffer.allocUnsafe(4);
        header[1] = 126;
        header.writeUInt16BE(body.length, 2);
    }
    else {
        header = Buffer.allocUnsafe(10);
        header[1] = 127;
        header.writeBigUInt64BE(BigInt(body.length), 2);
    }
    header[0] = 0x80 | (opcode & 0x0f);
    return body.length ? Buffer.concat([header, body]) : header;
}

function websocketClosePayload(code, reason = '') {
    let text = Buffer.from(String(reason), 'utf8');
    if (text.length > 123) {
        text = text.subarray(0, 123);
    }
    const out = Buffer.allocUnsafe(2 + text.length);
    out.writeUInt16BE(code, 0);
    text.copy(out, 2);
    return out;
}

class WebSocketRelaySocket extends EventEmitter {
    constructor(raw, maxMessageBytes) {
        super();
        this.raw = raw;
        this.remoteAddress = raw.remoteAddress;
        this.remotePort = raw.remotePort;
        this.destroyed = false;
        this.writable = true;
        this.buffer = Buffer.alloc(0);
        this.fragmentOpcode = 0;
        this.fragmentParts = [];
        this.fragmentBytes = 0;
        this.maxMessageBytes = maxMessageBytes;
        this.timeoutMs = 0;
        this.timeoutCallback = null;
        this.timeoutTimer = null;
        this.sentClose = false;
        this.gotClose = false;
        this.ended = false;
        raw.on('data', (chunk) => {
            if (this.destroyed || !chunk?.length) return;
            this._touch();
            this.buffer = this.buffer.length ? Buffer.concat([this.buffer, chunk]) : Buffer.from(chunk);
            this._parse();
        });
        raw.on('end', () => this._emitEnd());
        raw.on('close', () => {
            if (this.destroyed) return;
            this.destroyed = true;
            this.writable = false;
            this._clearTimeout();
            this._emitEnd();
            this.emit('close');
        });
        raw.on('error', (err) => {
            if (this.listenerCount('error')) this.emit('error', err);
        });
    }
    feedHead(head) {
        if (!head?.length || this.destroyed) return;
        this.buffer = this.buffer.length ? Buffer.concat([this.buffer, head]) : Buffer.from(head);
        this._parse();
    }
    setNoDelay(value = true) {
        this.raw.setNoDelay(value);
        return this;
    }
    setTimeout(ms, callback) {
        this.timeoutMs = Number(ms) || 0;
        this.timeoutCallback = typeof callback === 'function' ? callback : null;
        this._touch();
        return this;
    }
    _clearTimeout() {
        if (this.timeoutTimer) clearTimeout(this.timeoutTimer);
        this.timeoutTimer = null;
    }
    _touch() {
        this._clearTimeout();
        if (this.timeoutMs > 0 && !this.destroyed) {
            this.timeoutTimer = setTimeout(() => {
                this.timeoutTimer = null;
                if (this.timeoutCallback && !this.destroyed) this.timeoutCallback();
            }, this.timeoutMs);
            this.timeoutTimer.unref?.();
        }
    }
    write(data, callback) {
        if (this.destroyed || !this.writable) {
            const err = new Error('socket is closed');
            err.code = 'EPIPE';
            if (callback) queueMicrotask(() => callback(err));
            return false;
        }
        const frame = websocketFrame(0x2, Buffer.from(data));
        this._touch();
        return this.raw.write(frame, callback);
    }
    _writeControl(opcode, payload = Buffer.alloc(0)) {
        if (this.destroyed || !this.writable) return;
        this._touch();
        this.raw.write(websocketFrame(opcode, payload));
    }
    _protocolError(reason) {
        if (!this.sentClose) {
            this.sentClose = true;
            this._writeControl(0x8, websocketClosePayload(1002, reason));
        }
        const err = new Error(`WebSocket protocol error: ${reason}`);
        err.code = 'EPROTO';
        if (this.listenerCount('error')) this.emit('error', err);
        this.destroy(err);
    }
    _messageTooLarge() {
        if (!this.sentClose) {
            this.sentClose = true;
            this._writeControl(0x8, websocketClosePayload(1009, 'message too large'));
        }
        this.destroy(new Error('WebSocket message too large'));
    }
    _parse() {
        try {
            while (!this.destroyed) {
                if (this.buffer.length < 2) return;
                const b0 = this.buffer[0];
                const b1 = this.buffer[1];
                const fin = Boolean(b0 & 0x80);
                const rsv = b0 & 0x70;
                const opcode = b0 & 0x0f;
                const masked = Boolean(b1 & 0x80);
                let length = b1 & 0x7f;
                let offset = 2;
                if (rsv) return this._protocolError('RSV bits are not supported');
                if (!masked) return this._protocolError('client frames must be masked');
                if (length === 126) {
                    if (this.buffer.length < 4) return;
                    length = this.buffer.readUInt16BE(2);
                    offset = 4;
                }
                else if (length === 127) {
                    if (this.buffer.length < 10) return;
                    const n = this.buffer.readBigUInt64BE(2);
                    if (n > BigInt(Number.MAX_SAFE_INTEGER)) return this._messageTooLarge();
                    length = Number(n);
                    offset = 10;
                }
                const control = opcode >= 0x8;
                if (control && (!fin || length > 125)) return this._protocolError('invalid control frame');
                if (length > this.maxMessageBytes) return this._messageTooLarge();
                if (this.buffer.length < offset + 4 + length) return;
                const mask = this.buffer.subarray(offset, offset + 4);
                offset += 4;
                const payload = Buffer.from(this.buffer.subarray(offset, offset + length));
                this.buffer = this.buffer.subarray(offset + length);
                for (let i = 0; i < payload.length; i++) payload[i] ^= mask[i & 3];
                if (opcode === 0x8) {
                    this.gotClose = true;
                    if (!this.sentClose) {
                        this.sentClose = true;
                        this._writeControl(0x8, payload);
                    }
                    this._emitEnd();
                    this.writable = false;
                    this.raw.end();
                    return;
                }
                if (opcode === 0x9) {
                    this._writeControl(0xA, payload);
                    continue;
                }
                if (opcode === 0xA) continue;
                if (opcode === 0x1) {
                    if (!this.sentClose) {
                        this.sentClose = true;
                        this._writeControl(0x8, websocketClosePayload(1003, 'binary frames only'));
                    }
                    this.raw.end();
                    return;
                }
                if (opcode === 0x2) {
                    if (this.fragmentOpcode) return this._protocolError('new data frame during fragmentation');
                    if (fin) this._emitBinary(payload);
                    else {
                        this.fragmentOpcode = opcode;
                        this.fragmentParts = [payload];
                        this.fragmentBytes = payload.length;
                    }
                    continue;
                }
                if (opcode === 0x0) {
                    if (!this.fragmentOpcode) return this._protocolError('unexpected continuation frame');
                    this.fragmentBytes += payload.length;
                    if (this.fragmentBytes > this.maxMessageBytes) return this._messageTooLarge();
                    this.fragmentParts.push(payload);
                    if (fin) {
                        const joined = Buffer.concat(this.fragmentParts, this.fragmentBytes);
                        this.fragmentOpcode = 0;
                        this.fragmentParts = [];
                        this.fragmentBytes = 0;
                        this._emitBinary(joined);
                    }
                    continue;
                }
                return this._protocolError(`unsupported opcode ${opcode}`);
            }
        }
        catch (err) {
            if (this.listenerCount('error')) this.emit('error', err);
            this.destroy(err);
        }
    }
    _emitBinary(payload) {
        if (payload.length) this.emit('data', payload);
    }
    _emitEnd() {
        if (this.ended) return;
        this.ended = true;
        this.emit('end');
    }
    destroy(error) {
        if (this.destroyed) return;
        this.destroyed = true;
        this.writable = false;
        this._clearTimeout();
        if (error && this.listenerCount('error')) this.emit('error', error);
        this.raw.destroy();
        this._emitEnd();
        this.emit('close');
    }
}

function rejectUpgrade(raw, status, message) {
    if (raw.destroyed) return;
    const body = Buffer.from(String(message || 'WebSocket upgrade rejected'), 'utf8');
    raw.end(`HTTP/1.1 ${status}\r\nConnection: close\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: ${body.length}\r\n\r\n${body}`);
}

function acceptWebSocketUpgrade(req, raw, head, cfg) {
    const upgrade = String(req.headers.upgrade || '').toLowerCase();
    const connection = String(req.headers.connection || '').toLowerCase();
    const key = String(req.headers['sec-websocket-key'] || '');
    const version = String(req.headers['sec-websocket-version'] || '');
    if (upgrade !== 'websocket' || !connection.split(',').some((v) => v.trim() === 'upgrade') || version !== '13') {
        rejectUpgrade(raw, '400 Bad Request', 'invalid WebSocket upgrade');
        return null;
    }
    let keyBytes;
    try { keyBytes = Buffer.from(key, 'base64'); }
    catch { keyBytes = Buffer.alloc(0); }
    if (keyBytes.length !== 16) {
        rejectUpgrade(raw, '400 Bad Request', 'invalid Sec-WebSocket-Key');
        return null;
    }
    if (cfg.wsPath) {
        let pathname = '/';
        try { pathname = new URL(req.url || '/', 'http://relay.invalid').pathname; }
        catch { }
        if (pathname !== cfg.wsPath) {
            rejectUpgrade(raw, '404 Not Found', 'not found');
            return null;
        }
    }
    const accept = websocketAccept(key);
    raw.write(
        'HTTP/1.1 101 Switching Protocols\r\n' +
        'Upgrade: websocket\r\n' +
        'Connection: Upgrade\r\n' +
        `Sec-WebSocket-Accept: ${accept}\r\n` +
        '\r\n'
    );
    const socket = new WebSocketRelaySocket(raw, cfg.maxWsMessageBytes);
    return { socket, head };
}

async function handleConnection(socket, cfg, xm) {
    const reader = new AsyncByteReader(socket);
    let established = false;
    socket.setNoDelay(true);
    socket.setTimeout(cfg.handshakeTimeout, () => socket.destroy(new Error('handshake timeout')));
    try {
        const control = await readControl(reader);
        established = true;
        socket.setTimeout(cfg.idleTimeout > 0 ? cfg.idleTimeout : 0, () => socket.destroy(new Error('idle timeout')));
        if (control.mode === RELAY_MODE_FIXED_UDP) {
            await serveDirectUDP(socket, reader, control.target);
        }
        else if (control.mode === RELAY_MODE_PACKET_UDP) {
            await servePacketUDP(socket, reader);
        }
        else {
            const mux = new MuxConnection(socket, reader, cfg, xm);
            await mux.serve();
        }
    }
    catch (err) {
        if (!established && !socket.destroyed) {
            await writeControlError(socket, 'malformed control header');
        }
        else if (!isNormalClose(err)) {
            console.error(`relay connection ${socket.remoteAddress || '?'}:${socket.remotePort || '?'}: ${err.message || err}`);
        }
    }
    finally {
        socket.destroy();
    }
}

function isNormalClose(err) {
    if (!err) {
        return true;
    }
    const code = err.code || '';
    if (['EOF', 'ECONNRESET', 'EPIPE', 'ERR_STREAM_PREMATURE_CLOSE'].includes(code)) {
        return true;
    }
    const msg = String(err.message || err).toLowerCase();
    return msg.includes('unexpected eof') || msg.includes('socket is closed') || msg.includes('idle timeout');
}

function createRelayServer(cfg = buildConfig()) {
    const xm = new XUDPManager(cfg.xudpGrace);
    let active = 0;
    const requestHandler = (_req, res) => {
        res.writeHead(426, {
            'content-type': 'text/plain; charset=utf-8',
            'connection': 'close',
            'upgrade': 'websocket',
        });
        res.end('WebSocket upgrade required\n');
    };
    const server = http.createServer(requestHandler);
    server.on('upgrade', (req, raw, head) => {
        if (active >= cfg.maxConns) {
            rejectUpgrade(raw, '503 Service Unavailable', 'server busy');
            return;
        }
        const accepted = acceptWebSocketUpgrade(req, raw, head, cfg);
        if (!accepted) return;
        const { socket, head: initial } = accepted;
        active++;
        let counted = true;
        socket.once('close', () => {
            if (counted) {
                counted = false;
                active--;
            }
        });
        handleConnection(socket, cfg, xm).catch((err) => {
            console.error('connection handler error', err?.stack || err);
            socket.destroy();
        });
        socket.feedHead(initial);
    });
    server.on('close', () => xm.close());
    server.xudpManager = xm;
    return server;
}

async function startRelay(overrides = {}) {
    const cfg = buildConfig(overrides);
    const server = createRelayServer(cfg);
    await new Promise((resolve, reject) => {
        server.once('error', reject);
        server.listen(cfg.listenAddress.port, cfg.listenAddress.host, () => {
            server.off('error', reject);
            resolve();
        });
    });
    return { server, cfg };
}

async function main() {
    const { server, cfg } = await startRelay();
    const addr = server.address();
    const scheme = 'ws';
    const path = cfg.wsPath || '/';
    console.log(`UDP-only/XUDP WebSocket relay listening on ${scheme}://${addr.address}:${addr.port}${path} auth=none xudp-grace=${cfg.xudpGrace}ms`);
    const shutdown = () => {
        server.close(() => process.exit(0));
        setTimeout(() => process.exit(1), 5000).unref();
    };
    process.once('SIGINT', shutdown);
    process.once('SIGTERM', shutdown);
}

if (require.main === module) {
    main().catch((err) => {
        console.error(err?.stack || err);
        process.exitCode = 1;
    });
}

module.exports = {
    CONFIG,
    ATYP_IPV4,
    ATYP_DOMAIN,
    ATYP_IPV6,
    RELAY_MAGIC,
    RELAY_MODE_FIXED_UDP,
    RELAY_MODE_MUX,
    RELAY_MODE_PACKET_UDP,
    MUX_STATUS_NEW,
    MUX_STATUS_KEEP,
    MUX_STATUS_END,
    MUX_OPTION_DATA,
    MUX_NETWORK_UDP,
    buildConfig,
    startRelay,
    createRelayServer,
    readMuxFrame,
    AsyncByteReader,
    encodeUDPSource,
};
