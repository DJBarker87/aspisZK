#!/usr/bin/env python3
"""Check the saved R724 null functional after exact source chord transpose."""
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).parent
P = 2_147_483_647
RESIDUAL = BASE / "all-code-pullback-result.json"
RAW = BASE / "remote-run/attempt-c-shifted/matrix.raw.tsv"
SOURCE = BASE / "source-pins/r17_opening_weights.rs"

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def add(x,y): return (x+y) % P
def mul(x,y): return (x*y) % P

def xt(v, n):
    out = []
    half = (P+1)//2
    for j in range(n):
        row, bit, scale, total = j, 0, 1, 0
        while row & (1 << bit):
            row ^= 1 << bit
            scale = mul(scale, half)
            total = add(total, mul(v[row], scale))
            bit += 1
        total = add(total, mul(v[row | (1 << bit)], scale))
        out.append(total)
    return out

def chord_transpose(w, a, b, c):
    assert len(w) == 1024
    w = w + [0, 0, 0, 0]
    wa = w[::2]
    wb = w[1::2]
    assert len(wa) == len(wb) == 514
    xwa, xxwa, xwb = xt(wa, 513), xt(xt(wa, 513), 512), xt(wb, 512)
    out = [0] * 1024
    for j in range(512):
        out[2*j] = add(add(mul(a, wa[j]), mul(b, xwa[j])), mul(c, wb[j]))
        out[2*j+1] = add(add(mul(c, (wa[j]-xxwa[j]) % P), mul(a, wb[j])), mul(b, xwb[j]))
    return out

res = json.loads(RESIDUAL.read_text())
L = [0] * 1024
for item in res["residuals"]:
    L[item["code_index"]] = item["residue"]
Lq = chord_transpose(L, 7, 5, P-5)

def pair_value(d, s):
    # Lq dot (pair(d,s,7)-pair(0,s,7)).
    seven_s = pow(7, s, P)
    return (Lq[4*d+s] - seven_s*Lq[4*d] - Lq[s] + seven_s*Lq[0]) % P

existing_list = []
for line in RAW.read_text().splitlines():
    if line.startswith("column\t"):
        _, _, d, s = line.split("\t")
        existing_list.append((int(d), int(s)))
assert len(existing_list) == 241
existing = set(existing_list)
existing_nonzero = [{"column": col, "pair": [d,s], "value": pair_value(d,s)}
                    for col,(d,s) in enumerate(existing_list) if pair_value(d,s)]
omitted = [(d,s,pair_value(d,s)) for d in range(22,255) for s in range(1,4)
           if (d,s) not in existing and pair_value(d,s)]
out = {
    "task": "R724 all-code null functional chord-transpose omitted-pair check",
    "modulus": P,
    "inputs_sha256": {str(p.relative_to(BASE)): sha(p) for p in [RESIDUAL, RAW, SOURCE]},
    "abc": [7,5,P-5],
    "all_code_residual_support": sum(x != 0 for x in L),
    "existing_column_count": len(existing_list),
    "existing_unique_pair_count": len(existing),
    "existing_pair_nonzero_count": len(existing_nonzero),
    "existing_pair_nonzero": existing_nonzero,
    "omitted_pair_nonzero_count": len(omitted),
    "first_omitted_nonzero": None if not omitted else {"pair": omitted[0][:2], "value": omitted[0][2]},
    "omitted_pair_nonzero": [{"pair": [d,s], "value": v} for d,s,v in omitted],
}
(BASE / "chord-transpose-omitted-pairs-result.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({k:out[k] for k in ["existing_pair_nonzero_count", "omitted_pair_nonzero_count", "first_omitted_nonzero"]}))
