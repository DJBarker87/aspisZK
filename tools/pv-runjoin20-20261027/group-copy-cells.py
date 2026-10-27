from pathlib import Path
import sys
L=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for start in range(0,81,9):
 imports=[];bodies=[]
 for j in range(max(1,start),start+9):
  p=Path(__file__).resolve().parents[2]/'evidence/pv-runjoin20-20261027/cell-drafts'/f'PV_RunJoin_CopyCell{j:02}20.lean.txt';s=p.read_text()
  imports.extend(l for l in s.splitlines() if l.startswith('import '));bodies.append(s[s.index('set_option'):])
 out='\n'.join(dict.fromkeys(imports))+'\n'+'\n'.join(bodies)
 p=L/f'PV_RunJoin_CopyGroup{start:02}20.lean'
 if '--check' in sys.argv:assert p.read_text()==out
 else:p.write_text(out)
print('nine named groups; no unrolled recurrences')
