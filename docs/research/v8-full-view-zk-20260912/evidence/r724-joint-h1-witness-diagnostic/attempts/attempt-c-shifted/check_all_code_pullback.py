#!/usr/bin/env python3
"""Exact base-M31 pullback check for the saved R724 shifted null vector.

This is deliberately a small, deterministic arithmetic check.  It evaluates
the listed linear functional on every standard code basis vector c=e_j using
the frozen R16 inverse transport and the selected `v6_statement_points`
definition.  It does not impose the diagnostic's fold/query restrictions.
"""
import hashlib
import json
import re
from pathlib import Path

BASE = Path(__file__).parent
P = 2_147_483_647
NULL = BASE / "left-nullspace.tsv"
TABLE = BASE / "source-pins/r17_basis_tables.rs"
TRANSPORT = BASE / "source-pins/r16_basis_transport.rs"
POINTS = BASE / "source-pins/v6_statement_points_excerpt.rs"

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def array_after(name, text, atom):
    m = re.search(rf"pub const {name}: \[[^\]]+; 1024\] = \[(.*?)\];", text, re.S)
    if not m:
        raise RuntimeError(f"could not parse {name}")
    xs = re.findall(atom, m.group(1))
    if len(xs) != 1024:
        raise RuntimeError(f"{name}: expected 1024 values, got {len(xs)}")
    return xs

table = TABLE.read_text()
order = list(map(int, array_after("ORDER", table, r"\d+")))
inactive = [x == "true" for x in array_after("INACTIVE", table, r"true|false")]
assert sorted(order) == list(range(1024))
assert order[1023] == 1023 and inactive[1023]

# The source's `shifted` branch in saved src/main.rs is
# [1,1,2,3,4,2,2,3,0,2]. `v6_statement_points` makes point 0 z and point 2
# z with coordinates 7 and 6 complemented.
z = [1, 1, 2, 3, 4, 2, 2, 3, 0, 2]
point0 = z[:]
point2 = z[:]
point2[7] = (1 - point2[7]) % P
point2[6] = (1 - point2[6]) % P

def tensor_weight(point, r):
    # WeightAccumulator.add_multilinear uses the first coordinate as bit 9.
    out = 1
    for k, value in enumerate(point):
        out = (out * (value if ((r >> (9-k)) & 1) else (1-value))) % P
    return out

w0 = [tensor_weight(point0, r) for r in range(1024)]
w2 = [tensor_weight(point2, r) for r in range(1024)]

# Read the exact saved left-null vector. Only its scalar/base-M31 limb is in
# scope here; all other limbs must be zero.
lam = [0] * 1024
point0_coeff = point2_coeff = None
for line in NULL.read_text().splitlines()[1:]:
    fields = line.split("\t")
    label = fields[1]
    limbs = list(map(int, fields[2:6]))
    assert limbs[1:] == [0, 0, 0], (label, limbs)
    a = limbs[0] % P
    if label.startswith("active_chord_"):
        lam[int(label.rsplit("_", 1)[1])] = a
    elif label == "point_0":
        point0_coeff = a
    elif label == "point_2":
        point2_coeff = a
    else:
        assert a == 0, (label, a)
assert point0_coeff == 1
assert point2_coeff == 715827882

def inverse_basis(j):
    """Exact `Transport::inverse` applied to t=e_j, as a sparse map."""
    m = {order[j]: 1}
    other = 1 if j != 1023 and inactive[order[j]] else 0
    pivot = ((1 if j == 1023 else 0) - other) % P
    if pivot:
        m[1023] = (m.get(1023, 0) + pivot) % P
    return {r: v for r, v in m.items() if v}

residuals = []
for j in range(1024):
    m = inverse_basis(j)
    p0 = sum(w0[r] * v for r, v in m.items()) % P
    p2 = sum(w2[r] * v for r, v in m.items()) % P
    residue = (lam[j] + point0_coeff*p0 + point2_coeff*p2) % P
    if residue:
        residuals.append({"code_index": j, "residue": residue,
                          "active_coefficient": lam[j], "point0_pullback": p0,
                          "point2_pullback": p2, "inverse_support": sorted(m)})

out = {
    "task": "R724 all-code shifted null-functional pullback",
    "modulus": P,
    "inputs_sha256": {str(p.relative_to(BASE)): sha(p) for p in [NULL, TABLE, TRANSPORT, POINTS]},
    "source_point_parameters": {"point0": point0, "point2": point2},
    "certificate": {"active_nonzero_count": sum(x != 0 for x in lam),
                    "point0": point0_coeff, "point2": point2_coeff},
    "checked_code_basis_count": 1024,
    "nonzero_residual_count": len(residuals),
    "residuals": residuals,
}
(BASE / "all-code-pullback-result.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({k: out[k] for k in ["checked_code_basis_count", "nonzero_residual_count"]}))
if residuals:
    print("first residual:", residuals[0])
