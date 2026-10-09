#!/usr/bin/env python3
"""Independent Python-bigint R0 oracle. No Rust output is read.

Run with --check to verify the checked-in kats.json byte for byte.
Field arithmetic uses schoolbook polynomials with i^2=-1, u^2=2+i.
"""
import argparse
import hashlib
import json
from pathlib import Path

P = 2**31 - 1
Q = P**4
E = P**8
ONE = (1, 0, 0, 0)


def digits(n, count):
    out = []
    for _ in range(count):
        n, d = divmod(n, P)
        out.append(d)
    assert n == 0
    return out


def add(a, b):
    return tuple((x + y) % P for x, y in zip(a, b))


def neg(a):
    return tuple(-x % P for x in a)


def mul(a, b):
    out = [0] * 4
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            ipow = (j % 2) + (k % 2)
            upow = (j // 2) + (k // 2)
            # u^2 becomes 2+i; reduce each resulting power of i.
            for extra_i, scale in ([(0, 2), (1, 1)] if upow == 2 else [(0, 1)]):
                power = ipow + extra_i
                out[(upow % 2) * 2 + power % 2] += x * y * scale * (-1) ** (power // 2)
    return tuple(x % P for x in out)


def power(a, n):
    result = ONE
    while n:
        if n & 1:
            result = mul(result, a)
        a = mul(a, a)
        n >>= 1
    return result


def circle(t, row):
    # All CM31 parameters, including both poles, use the row fallback.
    if t[2:] == [0, 0]:
        t = [row, 0, 1, 0]
    square = mul(t, t)
    denominator = add(ONE, square)
    inverse = power(denominator, Q - 2)
    assert mul(denominator, inverse) == ONE
    x = mul(add(ONE, neg(square)), inverse)
    y = mul(add(t, t), inverse)
    assert add(mul(x, x), mul(y, y)) == ONE
    return {"x": x, "y": y}


def sample(block):
    rank = int.from_bytes(block, "little")
    qm = digits(rank % Q, 4)
    return {
        "block_hex": block.hex(),
        "rank": str(rank),
        "mod_p4": str(rank % Q),
        "mod_p8": str(rank % E),
        "mod_p8_minus_one": str(rank % (E - 1)),
        "qm31": qm,
        "ordinary": digits(rank % E, 8),
        "gamma": digits(rank % (E - 1) + 1, 8),
        "circle0": circle(qm, 0),
        "circle1": circle(qm, 1),
    }


def scan(blocks):
    accepted = []
    draws = 0
    consumed = 0
    for block in blocks[:8]:
        if draws == 64:
            break
        consumed += 1  # squeeze AND advance before the word scan
        for offset in range(0, 32, 4):
            if len(accepted) == 22 or draws == 64:
                return {"accepted": accepted, "draws": draws, "blocks": consumed, "ok": len(accepted) == 22}
            draws += 1
            word = int.from_bytes(block[offset:offset + 4], "little") & (2**18 - 1)
            if word not in accepted:
                accepted.append(word)
    return {"accepted": accepted, "draws": draws, "blocks": consumed, "ok": len(accepted) == 22}


def query_case(name, words):
    assert len(words) == 64
    raw = b"".join(w.to_bytes(4, "little") for w in words)
    blocks = [raw[i:i + 32] for i in range(0, 256, 32)]
    return {"name": name, "blocks_hex": [b.hex() for b in blocks], **scan(blocks)}


def build():
    values = [("zero", 0), ("all_ff", 2**256 - 1),
              ("ascending", int.from_bytes(bytes(range(32)), "little")),
              ("descending", int.from_bytes(bytes(reversed(range(32))), "little")),
              ("high_bit", 2**255), ("alternating", int.from_bytes(b"\xaa\x55" * 16, "little"))]
    for name, n in [("p", P), ("p2", P**2), ("p4", Q), ("p8", E), ("p8_minus_one", E - 1)]:
        for delta in [-1, 0, 1]:
            values.append((f"{name}_{delta:+d}", n + delta))
    for bit in range(32, 256, 32):
        values.append((f"carry_{bit}", 2**bit - 1))
    # t=i and -i are the two singular parameters; u and 1+u are fallbacks.
    values += [("minus_i", P * (P - 1)), ("one_plus_u", P**2 + 1),
               ("decode_order", sum((i + 1) * P**i for i in range(8)))]
    cases = [{"name": name, **sample(n.to_bytes(32, "little"))} for name, n in values]
    queries = []
    for last in range(22, 65):
        words = list(range(21)) + [0] * 43
        words[last - 1] = 21
        queries.append(query_case(f"success_draw_{last}", words))
    queries += [query_case("exhaust_21", list(range(21)) + [0] * 43),
                query_case("exhaust_one", [0xffffffff] * 64),
                query_case("masked_descending", [(63 - i) | 0xfffc0000 for i in range(64)]),
                query_case("masked_duplicates", [(i // 2) | ((i % 2) << 18) for i in range(64)])]
    # Independent SHA-256 row framing KAT. Empty messages include all rows
    # without a protocol message; other byte strings are synthetic fixtures,
    # not S1's still-unfrozen canonical message schema.
    lengths = {0: 32, 2: 158, 14: 159, 25: 512, 26: 1, 27: 32, 28: 32, 30: 32, 31: 32}
    lengths.update({row: 16 for row in range(15, 25)})
    state = bytes(32)
    rows = []
    for row in range(32):
        message = bytes((row + i) % 256 for i in range(lengths.get(row, 0)))
        state = hashlib.sha256(state + bytes([0, 0x80 + row]) + message).digest()
        post_absorb = state
        if row == 31:
            blocks, states = [], []
            for _ in range(8):
                blocks.append(hashlib.sha256(state + b"\x01").digest())
                state = hashlib.sha256(state + b"\x02").digest()
                states.append(state)
            result = scan(blocks)
            state = states[result["blocks"] - 1]
        else:
            block = hashlib.sha256(state + b"\x01").digest()
            state = hashlib.sha256(state + b"\x02").digest()
            decoded = sample(block)
            kind = "qm31" if row < 25 else (f"circle{row - 25}" if row < 27 else ("gamma" if row == 27 else "ordinary"))
            result = {"kind": kind, "value": decoded[kind]}
        rows.append({"row": row, "label": 0x80 + row, "message_hex": message.hex(),
                     "post_absorb_hex": post_absorb.hex(), "state_hex": state.hex(), "result": result})
    return {"provisional_framing": "state || 0x00 || (0x80 + row) || canonical_message; pending S1 SPEC.md",
            "p": P, "p4": str(Q), "p8": str(E), "samplers": cases, "queries": queries, "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = Path(__file__).with_name("kats.json")
    encoded = json.dumps(build(), indent=2) + "\n"
    if args.check:
        if target.read_text() != encoded:
            raise SystemExit("KAT mismatch; regenerate deliberately")
        print("kats.json matches independent Python-bigint oracle")
    else:
        target.write_text(encoded)
        print(f"wrote {target.name}")


if __name__ == "__main__":
    main()
