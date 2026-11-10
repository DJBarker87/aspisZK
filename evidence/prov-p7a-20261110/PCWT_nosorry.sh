#!/bin/bash
# usage: bash PCWT_nosorry.sh Funs.lean  -- write <name>_nosorry.lean without the declaration blocks that contain sorry (failed Aeneas bodies); the original is removed
python3 -B - "$1" <<'P'
import re,sys
f=sys.argv[1];t=open(f).read()
blocks=re.split(r'(?m)^(?=/--)',t);keep=[];drop=[]
for b in blocks:
    if 'sorry' in b:
        drop.append(re.findall(r'(?m)^def (\S+)',b))
    else:keep.append(b)
out=f.replace('.lean','_nosorry.lean');open(out,'w').write(''.join(keep));print(out,'dropped',drop)
P
