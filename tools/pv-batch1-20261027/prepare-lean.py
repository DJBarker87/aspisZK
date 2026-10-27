"""Preserve raw emissions and record the minimal pinned-backend API ports."""
from pathlib import Path
import re,json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch1-20261027');O=H/'lean';O.mkdir(exist_ok=True);rows=[]
for op in [230,254,258]:
 for phase in ['Types','Funs']:
  p=H/f'generated-{op}'/(phase+'.lean');raw=p.read_text();s=raw;ports=[]
  if phase=='Funs':
   old=f'import PVB1{op}.Types';assert s.count(old)==1;s=s.replace(old,f'import PV_B1_{op}_Types');ports.append(dict(kind='module import naming',old=old,new=f'import PV_B1_{op}_Types'))
   for line in s.splitlines():
    if 'wrapping_sh' in line and '#i32' in line:
     new=re.sub(r'(\d+)#i32',r'\1#u32',line);ports.append(dict(kind='positive shift literal',old=line,new=new));s=s.replace(line,new)
   if op==258:
    old='    let i4 ← lift (Std.U16.wrapping_shl 1#u16 i3)'
    assert s.count(old)==1
    new='    let shift ← lift (UScalar.cast .U32 i3)\n    let i4 ← lift (Std.U16.wrapping_shl 1#u16 shift)'
    s=s.replace(old,new);ports.append(dict(kind='masked shift-count cast',old=old,new=new))
  names=re.findall(r'\b(?:def|structure) ([\w.]+)',s)
  end=f'end PV_B1_{op}';assert s.count(end)==1
  s=s.replace(end,'\n'.join('#print axioms '+x for x in names)+'\n'+end)
  dst=O/f'PV_B1_{op}_{phase}.lean';dst.write_text(s)
  rows.append(dict(module=dst.stem,raw=str(p),raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),ported_sha256=hashlib.sha256(s.encode()).hexdigest(),ports=ports,axiom_queries=names))
(H/'backend-ports.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([dict(module=r['module'],ports=len(r['ports']),declarations=len(r['axiom_queries'])) for r in rows]),flush=True)
