#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Автономная самопроверка pyWDTT.pyw: только стандартная библиотека.

Проверяет встроенную криптографию на официальных тестовых векторах и
сквозные сценарии клиента (обфускация RTP, WireGuard AEAD, record layer DTLS).
Запускать рядом с pyWDTT.pyw или pyWDTT-universal.py:

    python3 selftest_offline.py            # какой бэкенд выбран автоматически
    QWDTT_CRYPTO=pure python3 selftest_offline.py   # принудительно встроенный
"""
import os
import sys

for _stream in (sys.stdout, sys.stderr):
    try:
        _stream.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

_target = next((os.path.join(HERE, n) for n in ("pyWDTT.pyw", "pyWDTT.py", "pyWDTT-universal.py", "qwdtt.py")
                if os.path.exists(os.path.join(HERE, n))), None)
if _target is None:
    raise SystemExit("не найден pyWDTT.pyw / pyWDTT-universal.py рядом с этим скриптом")
from importlib.machinery import SourceFileLoader   # noqa: E402
import importlib.util                              # noqa: E402
_loader = SourceFileLoader("pyWDTT", _target)
m = importlib.util.module_from_spec(
    importlib.util.spec_from_loader("pyWDTT", _loader))
sys.modules["pyWDTT"] = m
_loader.exec_module(m)
sys.stdout = sys.__stdout__   # pyWDTT уводит stdout в свой лог-файл
sys.stderr = sys.__stderr__

fails = []


def check(name, cond, extra=""):
    print(("  ok   " if cond else "  FAIL ") + name + ((" — " + extra) if (extra and not cond) else ""))
    if not cond:
        fails.append(name)


print("Бэкенд криптографии:", m.CRYPTO_BACKEND)
print()

# ── AES-128-GCM, NIST SP 800-38D, Test Case 2 ─────────────────────────────
print("AES-GCM (NIST SP 800-38D):")
ct = m.AESGCM(bytes(16)).encrypt(bytes(12), bytes(16), None)
check("test case 2", ct.hex() == "0388dace60b6a392f328c2b971b2fe78"
                              "ab6e47d42cec13bdf53a67b21257bddf", ct.hex())

# ── AES-128-GCM, Test Case 4 (с AAD) ──────────────────────────────────────
key = bytes.fromhex("feffe9928665731c6d6a8f9467308308")
iv = bytes.fromhex("cafebabefacedbaddecaf888")
pt = bytes.fromhex("d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72"
                   "1c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39")
aad = bytes.fromhex("feedfacedeadbeeffeedfacedeadbeefabaddad2")
ct = m.AESGCM(key).encrypt(iv, pt, aad)
check("test case 4 (шифрование)", ct.hex().startswith("42831ec2217774244b7221b784d0d49c")
      and ct.hex().endswith("5bc94fbc3221a5db94fae95ae7121a47"), ct.hex()[:32])
check("test case 4 (расшифровка)", m.AESGCM(key).decrypt(iv, ct, aad) == pt)
try:
    m.AESGCM(key).decrypt(iv, ct[:-1] + bytes([ct[-1] ^ 1]), aad)
    check("подмена тега отклоняется", False)
except m.InvalidTag:
    check("подмена тега отклоняется", True)

# ── ChaCha20-Poly1305, RFC 8439 §2.8.2 ────────────────────────────────────
print("ChaCha20-Poly1305 (RFC 8439):")
key = bytes(range(0x80, 0xA0))
nonce = bytes.fromhex("070000004041424344454647")
aad = bytes.fromhex("50515253c0c1c2c3c4c5c6c7")
pt = (b"Ladies and Gentlemen of the class of '99: If I could offer you only one "
      b"tip for the future, sunscreen would be it.")
out = m.ChaCha20Poly1305(key).encrypt(nonce, pt, aad)
check("AEAD-тег", out.hex().endswith("1ae10b594f09e26a7e902ecbd0600691"), out.hex()[-32:])
check("расшифровка", m.ChaCha20Poly1305(key).decrypt(nonce, out, aad) == pt)

# ── X25519, RFC 7748 §5.2 ─────────────────────────────────────────────────
print("X25519 (RFC 7748):")
scalar = bytes.fromhex("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
point = bytes.fromhex("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c")
priv = m.x25519.X25519PrivateKey.from_private_bytes(scalar)
pub = m.x25519.X25519PublicKey.from_public_bytes(point)
check("скалярное умножение", priv.exchange(pub).hex() ==
      "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552",
      priv.exchange(pub).hex())
a, b = m.WgKeyPair(), m.WgKeyPair()
check("общий секрет совпадает", a.dh(b.public) == b.dh(a.public))
check("публичный ключ 32 байта", len(a.public) == 32)

# ── ECDH P-256 ────────────────────────────────────────────────────────────
print("ECDH на P-256:")
ka = m.ec.generate_private_key(m.ec.SECP256R1())
kb = m.ec.generate_private_key(m.ec.SECP256R1())
enc = m.serialization.Encoding.X962
fmt = m.serialization.PublicFormat.UncompressedPoint
pubb = kb.public_key().public_bytes(enc, fmt)
check("несжатая точка 65 байт", len(pubb) == 65 and pubb[0] == 4)
peer = m.ec.EllipticCurvePublicKey.from_encoded_point(m.ec.SECP256R1(), pubb)
pub_a = ka.public_key().public_bytes(enc, fmt)
peer_a = m.ec.EllipticCurvePublicKey.from_encoded_point(m.ec.SECP256R1(), pub_a)
check("общий секрет совпадает 32 байта",
      ka.exchange(m.ec.ECDH(), peer) == kb.exchange(m.ec.ECDH(), peer_a)
      and len(ka.exchange(m.ec.ECDH(), peer)) == 32)

# ── Обфускация RTP и WireGuard ────────────────────────────────────────────
print("Туннель:")
wkey = m.derive_wrap_key("тестовый-пароль")
for mode in ("audio", "video"):
    cfg = m.ObfsConfig(mode)
    state = m.ObfsState()
    ok = True
    for size in (1, 100, 1100):
        payload = os.urandom(size)
        wire = m.obfs_wrap_packet(wkey, payload, cfg, state)
        ok = ok and m.obfs_is_rtp_packet(wire) and m.obfs_unwrap_packet(wkey, wire) == payload
    check("RTP-обфускация (%s)" % mode, ok)

k = os.urandom(32)
check("WireGuard AEAD", m.wg_aead_open(k, m.wg_aead_seal(k, b"data", b"ad"), b"ad") == b"data")
try:
    m.wg_aead_open(k, m.wg_aead_seal(k, b"data", b"ad"), b"other-ad")
    check("WireGuard AEAD отклоняет подделку", False)
except m.InvalidTag:
    check("WireGuard AEAD отклоняет подделку", True)


class _Pipe(object):
    def __init__(self):
        self.buf = []

    def send(self, data):
        self.buf.append(data)

    def recv(self, timeout=1.0):
        return self.buf.pop(0) if self.buf else None


pipe = _Pipe()
sender = m.DtlsClient(pipe)
receiver = m.DtlsClient(_Pipe())
for c in (sender, receiver):
    c.read_keys = c.write_keys = os.urandom(16)
    c.read_iv = c.write_iv = os.urandom(4)
    c.epoch_read = c.epoch_write = 1
    c._aead_read = c._aead_write = None
receiver.read_keys = sender.write_keys
receiver.read_iv = sender.write_iv
payload = os.urandom(900)
sender._send_record(m.DTLS_CT_APPDATA, payload)
parsed = receiver._parse_record(pipe.buf[0])
check("record layer DTLS 1.2", bool(parsed) and parsed[0][3] == payload)

print()
if fails:
    print("ПРОВАЛОВ: %d — %s" % (len(fails), ", ".join(fails)))
    sys.exit(1)
print("Все проверки пройдены ✓")
