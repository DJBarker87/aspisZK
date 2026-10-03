#!/usr/bin/env python3
import hashlib, json, pathlib, struct
P = 2147483647
path = pathlib.Path(__file__).parent / 'remote/g-left-kernel-rerun.bin'
b = path.read_bytes()
magic = b'R117GLEFTKERNEL1\0'
assert b[:len(magic)] == magic, (b[:len(magic)], magic)
off = len(magic)
rows, cols = struct.unpack_from('<II', b, off); off += 8
assert (rows, cols) == (626, 1022)
words = (rows*cols + rows + rows)*4
assert len(b) == off + words*4, (len(b), off + words*4)
def getq(buf, pos):
    x = struct.unpack_from('<4I', buf, pos)
    assert all(v < P for v in x), x
    return x
# Quartic basis c0.a,c0.b,c1.a,c1.b; CM31 i^2=-1 and QM31 u^2=2+i.
def add(a,b): return tuple((x+y)%P for x,y in zip(a,b))
def sub(a,b): return tuple((x-y)%P for x,y in zip(a,b))
def cmul(a,b):
    aa,ab=a; ba,bb=b
    return ((aa*ba-ab*bb)%P, (aa*bb+ab*ba)%P)
def r_times(x):
    a,b=x
    return ((2*a-b)%P, (a+2*b)%P)
def qmul(x,y):
    a=x[:2]; b=x[2:]; c=y[:2]; d=y[2:]
    ac=cmul(a,c); bd=cmul(b,d); ad=cmul(a,d); bc=cmul(b,c)
    first=add(ac,r_times(bd)); second=add(ad,bc)
    return first+second
pos=off
matrix=[]
for _ in range(rows):
    row=[]
    for _ in range(cols): row.append(getq(b,pos)); pos+=16
    matrix.append(row)
target=[]
for _ in range(rows): target.append(getq(b,pos)); pos+=16
coeff=[]
for _ in range(rows): coeff.append(getq(b,pos)); pos+=16
nz=[(i,x) for i,x in enumerate(coeff) if x!=(0,0,0,0)]
# Check exact left-kernel relation on all original columns.
for j in range(cols):
    s=(0,0,0,0)
    for i,c in nz: s=add(s,qmul(c,matrix[i][j]))
    assert s==(0,0,0,0), (j,s)
rhs=(0,0,0,0)
for i,c in nz: rhs=add(rhs,qmul(c,target[i]))
assert rhs!=(0,0,0,0)
groups=[sum(lo<=i<=hi for i,_ in nz) for lo,hi in [(0,270),(271,358),(359,361),(362,617),(618,618),(619,624),(625,625)]]
print(json.dumps({
 'path':str(path), 'sha256':hashlib.sha256(b).hexdigest(), 'magic':magic.decode('ascii','backslashreplace'),
 'rows':rows,'columns':cols,'nonzero_coefficients':[[i,list(x)] for i,x in nz],
 'support_groups_semantic_raw_point_final_balance_relation_p2':groups,
 'rhs_quartic_limbs':list(rhs), 'all_1022_original_columns_zero':True,
 'rhs_nonzero':True,'file_bytes':len(b)
},indent=2))
