"""Prepare private import-narrowed copies; never edit an emitted definition.

The owned cohort preserves declaration names and bodies and replaces only
module imports. Carrier aliases need FullTypes, not the unrelated BodyFibre
installation imported by the historical carrier. This is an explicit new
proof cohort, not an assertion that historical object files were replayed.
"""
from pathlib import Path
import subprocess,json,re,hashlib
R=Path(__file__).resolve().parents[2];P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdb2-20261028'
j=json.loads((E/'V240-applied-resolution.json').read_text())['modules']
mapping={
 'R1Z.ProverRwFullExternalTypes':'R1Z.PV_RDB2_FullExternalTypes',
 'R1Z.ProverRwFullTypes':'R1Z.PV_RDB2_FullTypes',
 'R1Z.ProverRwFullExternalFuns':'R1Z.PV_RDB2_FullExternalFuns',
 'R1Z.ProverRwFullFuns':'R1Z.PV_RDB2_FullFuns',
 'R1Z.ProverRwP6CompressSource':'R1Z.PV_RDB2_P6CompressSource',
 'R1Z.PV_Op223_Carrier':'R1Z.PV_RDB2_AppliedCarrier',
}
for m in j:
 if m.startswith('R1Z.PV_Op223_Extract_'):mapping[m]=m.replace('PV_Op223_Extract_','PV_RDB2_Applied_')
rows=[]
for old,new in mapping.items():
 r=j[old];raw=subprocess.check_output(['git','show',r['blob']],cwd=R);assert hashlib.sha256(raw).hexdigest()==r['sha256']
 text=raw.decode()
 def change(match):
  imp=match[1]
  if old=='R1Z.PV_Op223_Carrier':
   assert imp=='R1Z.PV_Ext_ClosedCarrier';return 'import R1Z.PV_RDB2_FullTypes'
  return 'import '+mapping.get(imp,imp)
 changed=re.sub(r'^import (\S+)',change,text,flags=re.M)
 assert re.sub(r'^import .*\n','',text,flags=re.M)==re.sub(r'^import .*\n','',changed,flags=re.M)
 p=P/(new.split('.')[-1]+'.lean');assert not p.exists();p.write_text(changed)
 rows.append(dict(module=new,original_module=old,source_authority=r,original_sha256=r['sha256'],owned_sha256=hashlib.sha256(changed.encode()).hexdigest(),changes='imports only; no declaration, proof, body or generated option edited',imports=re.findall(r'^import (\S+)',changed,re.M)))
# topological order only for this new cohort
byname={r['module']:r for r in rows};order=[];seen=set()
def visit(m):
 if m in seen or m not in byname:return
 seen.add(m)
 for n in byname[m]['imports']:visit(n)
 order.append(m)
for m in byname:visit(m)
(E/'V240-owned-cone.json').write_text(json.dumps(dict(rows=rows,order=order,cohort='new owned import-narrowed cohort; source definitions and theorem text unchanged'),indent=2)+'\n')
print(len(order),'owned modules')
