from pathlib import Path
import subprocess,json,hashlib
D=Path('evidence/pv-rdeac-20261028');root=Path('docs/research/v8-r0-zk-20261009/lean')
def show(p):return subprocess.check_output(['git','show','HEAD:'+p],text=True)
manifest=json.loads(show('evidence/pv-cblib-20261027/manifest9-source-pins.json'))
pins={r['module'].replace('/','.'):r for r in manifest['modules']}
known={r['module'] for r in json.load(open('evidence/pv-rdea-20261028/actual-closure-final.json'))}
known.update(['R1Z.PV_CBL_JoinSlices','R1Z.PV_CBL_JoinAdapter'])
rows={};order=[]
def visit(m):
 if m in known or m in rows or not m.startswith('R1Z.'):return
 p=root/(m.replace('.','/')+'.lean');raw=p.read_bytes();sh=hashlib.sha256(raw).hexdigest();pin=pins[m];assert sh==pin['sha256'],m
 record=json.loads(show(f"evidence/pv-cblib-20261027/{pin['receipt']}.json"))
 assert record['exit']==0 and record['source_sha256']==sh,m
 deps=record['dependency_objects'];imports=[]
 for line in raw.decode().splitlines():
  if line.startswith('import '):imports.extend(line[7:].split())
 rows[m]=dict(module=m,path=str(p),source_sha256=sh,blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p)],text=True).strip(),receipt=pin['receipt'],record=record,imports=imports)
 for dep in imports:visit(dep)
 order.append(m)
visit('R1Z.PV_CBL_CallbackPublication')
expected={};conflicts=[]
for m,r in rows.items():
 for dep,d in r['record']['dependency_objects'].items():
  if dep in expected and expected[dep]['sha256']!=d['sha256']:conflicts.append(dict(module=dep,first=expected[dep],second=d,parent=m))
  expected[dep]=d
result=dict(modules=list(rows.values()),order=order,expected=expected,conflicts=conflicts,root='R1Z.PV_CBL_CallbackPublication',policy='Reuse only matching source, object and complete transitive dependency fingerprint; independently recompile the publication root against current Appendix/FullTypes objects.')
(D/'publication-inputs.json').write_text(json.dumps(result,indent=2)+'\n')
print('modules',len(order),'hash conflicts',len(conflicts))
