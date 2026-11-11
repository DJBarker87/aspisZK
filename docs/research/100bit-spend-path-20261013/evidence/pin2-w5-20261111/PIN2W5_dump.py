"""Parser for the pin2-w5-dump text format (lead tooling).
  V <stage> <seq> <tag> <index> <hex32>   trace::value; hex32 is WideExact::to_le_bytes
                                          = 8 little-endian u32 limbs (c0.a,c0.b,c1.a,c1.b of
                                          the first QM31, then the same for the second)
  H <stage> <seq> <part lengths> <input hex> <output hex>   one SHA-256 call
  R <key> <value>
"""
from collections import defaultdict
def limbs(h):
    b = bytes.fromhex(h); return [int.from_bytes(b[i:i+4], 'little') for i in range(0, len(b), 4)]
class Dump:
    def __init__(self, path):
        self.v = defaultdict(list); self.h = defaultdict(list); self.r = {}
        for line in open(path):
            p = line.split()
            if p[0] == 'V':
                self.v[p[1]].append((int(p[3]), int(p[4]), limbs(p[5])))
            elif p[0] == 'H':
                lens = [int(x) for x in p[3].split(',')] if p[3] else []
                inp = bytes.fromhex(p[4]) if len(p) == 6 else b''
                self.h[p[1]].append((lens, inp, bytes.fromhex(p[-1])))
            elif p[0] == 'R':
                self.r[p[1]] = ' '.join(p[2:])
    def tag(self, stage, t):
        """{index: limbs} for one tag; asserts each index is written once."""
        out = {}
        for tg, i, x in self.v[stage]:
            if tg == t:
                assert i not in out, (stage, t, i); out[i] = x
        return out
    def tag_last(self, stage, t):
        out = {}
        for tg, i, x in self.v[stage]:
            if tg == t: out[i] = x
        return out
