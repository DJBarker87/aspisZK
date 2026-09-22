#!/usr/bin/env python3
"""Exact integer check of the 64-group carry transpose, not a field sample.

Both maps are scaled by 64, sufficient for the longest six-half carry chain.
The source convention zero-extends reads at index 64; it is not cyclic.
"""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
def ones(j):
    n=0
    while j&1:n+=1;j>>=1
    return n
def basis(j):return [64 if i==j else 0 for i in range(64)]
forward=[]
for j in range(64):
    value=basis(j+1);bits=ones(j)
    while bits:
        bits-=1;row=j&~((1<<(bits+1))-1);term=basis(row)
        assert all((x+y)%2==0 for x,y in zip(value,term))
        value=[(x+y)//2 for x,y in zip(value,term)]
    forward.append(value)
transpose=[[0]*64 for _ in range(64)]
for j in range(64):
    value=64
    for bit in range(ones(j)):
        assert value%2==0;value//=2
        row=j&~((1<<(bit+1))-1);transpose[row][j]+=value
    if j+1<64:transpose[j+1][j]+=value
assert all(transpose[i][j]==forward[j][i]for i in range(64)for j in range(64))
report={'exact_integer_entries_checked':4096,'common_scale':64,'zero_extension_at_64':True,
        'max_carry_halves':6,'transpose_identity':True,'rust_refinement_proved':False,
        'forward_matrix_sha256':hashlib.sha256(json.dumps(forward,separators=(',',':')).encode()).hexdigest(),
        'boundary_rows':{str(j):[(i,x)for i,x in enumerate(forward[j])if x]for j in [0,1,3,31,63]}}
if a.output:
    assert not a.output.exists();a.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
