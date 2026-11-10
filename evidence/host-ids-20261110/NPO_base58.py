#!/usr/bin/env python3
"""NPO_: decode Solana base58 pubkeys with the Bitcoin/Solana alphabet (no checksum).
Usage: NPO_base58.py ID...   prints JSON {id: [32 bytes]}; --lean prints Lean literals."""
import json, sys
ALPHA = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58decode(s):
    n = 0
    for ch in s:
        n = n * 58 + ALPHA.index(ch)
    body = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    lead = len(s) - len(s.lstrip("1"))
    out = b"\x00" * lead + body
    assert len(out) == 32, (s, len(out))
    return out
def b58encode(b):
    n = int.from_bytes(b, "big"); s = ""
    while n: n, r = divmod(n, 58); s = ALPHA[r] + s
    return "1" * (len(b) - len(b.lstrip(b"\x00"))) + s
if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    res = {}
    for a in args:
        b = b58decode(a); assert b58encode(b) == a
        res[a] = list(b)
    if "--lean" in sys.argv:
        for a, b in res.items():
            print(a, "[" + ", ".join(f"{x}#u8" for x in b) + "]")
    else:
        print(json.dumps(res, indent=1))
