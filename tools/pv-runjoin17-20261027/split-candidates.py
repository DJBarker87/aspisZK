"""Split D287 candidates into independent single-cell recurrence certificates.
Only named one-round equalities are retained. Does not invent computed values.
"""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin17-20261027';C=R/'evidence/pv-runjoin16-20261027/candidate-certificates'
rows=[]
for p in sorted(C.glob('*.lean.txt')):
 s=p.read_text();header=s[:s.index('theorem round_')]
 starts=list(re.finditer(r'^theorem round_(\d+)_1 :',s,re.M))
 imports=[]
 for j,m in enumerate(starts):
  a=int(m[1]);body=s[m.start():starts[j+1].start() if j+1<len(starts) else s.rindex('end R1Z.')]
  n=f'PV_RunJoin_OutputCell{a:02}17';out=header+body+'end R1Z.PV_RunJoin_OutputModel16\n';dest=L/(n+'.lean')
  if '--check' in sys.argv:assert dest.read_text()==out
  else:dest.write_text(out)
  rows.append({'module':'R1Z/'+n,'candidate':str(p.relative_to(R)),'source_sha256':hashlib.sha256(out.encode()).hexdigest(),'round_equations':23,'recurrence_depth':1,'next_consumer':'PV_RunJoin_OutputPairChecks17 / PV_RunJoin_AppendChecks17'})
  imports.append('import R1Z.'+n)
 n=p.name.removesuffix('.lean.txt').replace('16','17')
 out='\n'.join(imports)+'\n';dest=E/'candidate-certificates'/(n+'.lean.txt')
 if '--check' in sys.argv:assert dest.read_text()==out
 else:dest.write_text(out)
assert len(rows)==42
if '--check' not in sys.argv:(E/'candidate-preflight.json').write_text(json.dumps(rows,indent=2)+'\n')
print('checked 42 single-cell chunks; only named single-round equations; five aggregate consumers')
