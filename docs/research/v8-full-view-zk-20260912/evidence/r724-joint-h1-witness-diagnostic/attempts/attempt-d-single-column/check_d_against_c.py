from pathlib import Path
P = 2_147_483_647
BASE = Path(__file__).parent.parent
C = BASE / "attempt-c-shifted/remote-run/attempt-c-shifted/matrix.raw.tsv"
D = Path(__file__).parent / "remote-run/attempt-d-shifted/matrix.raw.tsv"
LAM = BASE / "attempt-c-shifted/left-nullspace.tsv"

def parse(path):
    lines = path.read_text().splitlines()
    header = lines[0]
    cols = []
    while len(cols) < (241 if "columns=241" in header else 242):
        f = lines[1 + len(cols)].split("\t")
        cols.append((int(f[2]), int(f[3])))
    rows = []
    for line in lines[1 + len(cols):]:
        f = line.split("\t")
        rows.append((int(f[1]), f[2], [tuple(map(int, x.split(","))) for x in f[3:]]))
    return header, cols, rows

hc, cc, cr = parse(C)
hd, dc, dr = parse(D)
assert hc == "rows=222 columns=241" and hd == "rows=222 columns=242"
assert dc[:241] == cc
assert dc[241] == (47, 3)
assert len(cr) == len(dr) == 222
for a, b in zip(cr, dr):
    assert a[:2] == b[:2]
    assert a[2] == b[2][:241]
    assert len(b[2]) == 242
lam = []
for line in LAM.read_text().splitlines()[1:]:
    f = line.split("\t")
    lam.append(tuple(map(int, f[2:6])))
assert len(lam) == 222
new_column = [row[2][241] for row in dr]
res = tuple(sum(lam[i][k] * new_column[i][k] for i in range(222)) % P for k in range(4))
assert res == (1_909_084_209, 0, 0, 0), res
print("PASS: D preserves all C columns 0..240 and all 222 rows byte-for-byte")
print("PASS: D appends exactly column index 241 = pair (47,3)")
print("PASS: C left-null covector dotted with the new D column is", res, "mod P")
print("D full-rank result is recorded in matrix.log; no left-nullspace basis is emitted when rank=222")
