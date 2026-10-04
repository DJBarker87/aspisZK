from pathlib import Path
import ast

BASE = Path(__file__).parent
RAW = BASE / "remote-run/attempt-c-shifted/matrix.raw.tsv"
LOG = BASE / "remote-run/matrix.log"
P = 2_147_483_647

line = next(x for x in LOG.read_text().splitlines() if x.startswith("R724_MATRIX "))
start = line.index("left_nullspace_limbs=") + len("left_nullspace_limbs=")
nullspace = ast.literal_eval(line[start:])
assert len(nullspace) == 1
lam = nullspace[0]
rows = []
for line in RAW.read_text().splitlines():
    if not line.startswith("row\t"):
        continue
    fields = line.split("\t")
    idx, label = int(fields[1]), fields[2]
    values = [tuple(map(int, field.split(","))) for field in fields[3:]]
    assert idx == len(rows) and len(values) == 241
    rows.append((label, values))
assert len(rows) == len(lam) == 222
assert all(len(entry) == 4 for entry in lam)
for col in range(241):
    residues = tuple(
        sum(lam[row][limb] * rows[row][1][col][limb] for row in range(222)) % P
        for limb in range(4)
    )
    assert residues == (0, 0, 0, 0), (col, residues)
print("PASS: one emitted left-null vector; all 241 raw columns yield four zero residues mod P")
print("nonzero support:")
for row, ((label, _), coeff) in enumerate(zip(rows, lam)):
    if any(coeff):
        print(row, label, *coeff)
