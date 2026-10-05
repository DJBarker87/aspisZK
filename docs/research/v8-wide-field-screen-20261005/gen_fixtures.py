#!/usr/bin/env python3
"""Fixtures for the wide-field screen probe.  usage: gen_fixtures.py <out-dir>
Every kernel fixture carries the expected result computed by fields.py."""
import hashlib, pathlib, struct, sys
from fields import *

def limbs_c(x): return list(x)
def limbs_q(x): return limbs_c(x[0]) + limbs_c(x[1])
def limbs_o(x): return limbs_q(x[0]) + limbs_q(x[1])
def limbs_h(x): return limbs_c(x[0]) + limbs_c(x[1]) + limbs_c(x[2])
def pack(words): return b"".join(struct.pack("<I", w) for w in words)

def rnd(tag, count):
    out, i = [], 0
    while len(out) < count:
        v = int.from_bytes(hashlib.sha256(f"SCRN/{tag}/{i}".encode()).digest()[:4], "little") & 0x7fffffff
        if v < P: out.append(v)
        i += 1
    return out
def rc(tag): a = rnd(tag, 2); return (a[0], a[1])
def rq(tag): return (rc(tag + "/0"), rc(tag + "/1"))
def ro(tag): return (rq(tag + "/0"), rq(tag + "/1"))
def rh(tag): return (rc(tag + "/0"), rc(tag + "/1"), rc(tag + "/2"))

def write(root, name, op, n, payload):
    body = b"SCRN" + bytes([op, 0, 0, 0]) + struct.pack("<I", n) + payload
    body += bytes(max(0, 72 - len(body)))
    folder = root / name; folder.mkdir(parents=True)
    (folder / "proof-1.bin").write_bytes(body)
    (folder / "public.bin").write_bytes(b"wide-field-screen-public")
    (folder / "transition.bin").write_bytes(b"wide-field-screen-no-settlement")
    (folder / "binding.bin").write_bytes(bytes(32))

def kernels(root):
    check_fields()
    for n in (1000, 2000):
        x, y = rq("x4"), rq("y4"); r = x
        for _ in range(n): r = qmul(r, y)
        write(root, f"mul4-{n}", 1, n, pack(limbs_q(x) + limbs_q(y) + limbs_q(r)))
        x, y = rh("x6"), rh("y6"); r = x
        for _ in range(n): r = hmul(r, y)
        write(root, f"mul6-{n}", 2, n, pack(limbs_h(x) + limbs_h(y) + limbs_h(r)))
        x, y = ro("x8"), ro("y8"); r = x
        for _ in range(n): r = omul(r, y)
        write(root, f"mul8-{n}", 3, n, pack(limbs_o(x) + limbs_o(y) + limbs_o(r)))
        s = rnd("s", 1)[0]
        x = rq("sx4"); r = x
        for _ in range(n): r = qscale(r, s)
        write(root, f"scale4-{n}", 4, n, pack(limbs_q(x) + [s] + limbs_q(r)))
        x = rh("sx6"); r = x
        for _ in range(n): r = hscale(r, s)
        write(root, f"scale6-{n}", 5, n, pack(limbs_h(x) + [s] + limbs_h(r)))
        x = ro("sx8"); r = x
        for _ in range(n): r = oscale(r, s)
        write(root, f"scale8-{n}", 6, n, pack(limbs_o(x) + [s] + limbs_o(r)))
    for n in (100, 200):
        x, y = rq("ix4"), rq("iy4"); r = x
        for _ in range(n): r = qadd(qinv(r), y)
        write(root, f"inv4-{n}", 7, n, pack(limbs_q(x) + limbs_q(y) + limbs_q(r)))
        x, y = ro("ix8"), ro("iy8"); r = x
        for _ in range(n):
            i = oinv(r); r = (qadd(i[0], y[0]), qadd(i[1], y[1]))
        write(root, f"inv8-{n}", 8, n, pack(limbs_o(x) + limbs_o(y) + limbs_o(r)))

def h26(*parts):
    h = hashlib.sha256()
    for part in parts: h.update(part)
    return h.digest()[:26]
def stream(tag, length):
    out, i = b"", 0
    while len(out) < length:
        out += hashlib.sha256(f"SCRN/leaf/{tag}/{i}".encode()).digest(); i += 1
    return out[:length]
BASE = {}
def base(channel):
    if channel not in BASE:
        BASE[channel] = [h26(b"SCRN/public/synthetic/leaf", bytes([channel]), struct.pack("<I", i)) for i in range(1 << 18)]
    return BASE[channel]
def tree(leaves):
    levels = [leaves]
    while len(levels[-1]) > 1:
        cur = levels[-1]
        levels.append([h26(b"\x18", *cur[i:i + 8]) for i in range(0, len(cur), 8)])
    return levels
def indices(q, seed):
    out, r = set(), seed + 1
    while len(out) < q:
        r ^= (r << 13) & (2**64 - 1); r ^= r >> 7; r ^= (r << 17) & (2**64 - 1)
        out.add(r % (1 << 18))
    return sorted(out)
def auth(root, q, w2, world):
    w1 = 437
    ids = indices(q, 0x5C12 + world)
    leaves = [list(base(1)), list(base(2))]
    opened = []
    for i in ids:
        a, b = stream(f"c1/{world}/{i}", w1), stream(f"c2/{w2}/{world}/{i}", w2)
        leaves[0][i], leaves[1][i] = h26(a), h26(b)
        opened.append((i, a, b))
    t1, t2 = tree(leaves[0]), tree(leaves[1])
    f1 = f2 = b""; positions = set(ids)
    for level in range(6):
        parents = sorted({x // 8 for x in positions})
        for parent in parents:
            for slot in range(8):
                child = parent * 8 + slot
                if child not in positions:
                    f1 += t1[level][child]; f2 += t2[level][child]
        positions = set(parents)
    payload = struct.pack("<III", w1, w2, len(f1) // 26) + t1[-1][0] + t2[-1][0]
    for i, a, b in opened: payload += struct.pack("<I", i) + a + b
    payload += f1 + f2
    write(root, f"auth-q{q}-w{w2}-world{world}", 10, q, payload)
    return len(f1) // 26, 12 + len(payload)

if __name__ == "__main__":
    root = pathlib.Path(sys.argv[1]); assert not root.exists()
    kernels(root)
    for q, w2 in ((22, 220), (32, 220), (32, 313), (32, 406)):
        for world in (0, 1):
            nodes, size = auth(root, q, w2, world)
            print(f"auth q={q} w2={w2} world={world} frontier_digests_per_tree={nodes} input_bytes={size}")
    print("fixtures written; synthetic public leaves; not Aspis proofs")
