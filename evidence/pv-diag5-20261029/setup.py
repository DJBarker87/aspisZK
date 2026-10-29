from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag5-20261029');P=D.parent/'codex-pv-diag3-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=json.loads((D/'cohort-plan.json').read_text());rows=json.loads((P/'resume-cache-preflight.json').read_text())['rows'];pins=json.loads((P/'project-resolution.json').read_text())['modules'];ext=json.loads((P/'external-authority.json').read_text());external={r['module'].replace('/','.'):r for r in ext}
needed=set()
def visit(m):
 if m in needed:return
 needed.add(m)
 for dep in (plan['source_pins'][m]['imports'] if m in plan['source_pins'] else rows[m].get('record_dependencies',{})):visit(dep)
visit('R1Z.PV_RunJoin_Deployed')
assert set(plan['affected'])<=needed
checked=[]
for m in sorted(needed-set(plan['affected'])):
 r=rows[m];p=Path(r['path']);assert sha(p)==r['sha256'],m
 if m in pins:assert r.get('source_sha256')==pins[m]['sha256'],m
 for dep,q in r.get('record_dependencies',{}).items():assert q['sha256']==rows[dep]['sha256'],(m,dep)
 checked.append(r)
for r in ext:assert sha(Path(r['path']))==r['object_sha256']
O=D/'objects';O.mkdir(exist_ok=True)
for m in needed-set(plan['affected']):
 if m in external:continue
 src=Path(rows[m]['path']);dst=O/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src)
 for a,b in [(Path(str(src)+'.server'),Path(str(dst)+'.server')),(Path(str(src)+'.private'),Path(str(dst)+'.private')),(src.with_suffix('.ir'),dst.with_suffix('.ir'))]:
  if a.is_file():b.symlink_to(a)
for m in plan['affected']:
 s=D/'sources'/(m.replace('.','/')+'.lean');s.parent.mkdir(parents=True,exist_ok=True);s.write_bytes((D/'source-inputs'/(m+'.lean.txt')).read_bytes());assert sha(s)==plan['source_pins'][m]['sha256']
env=json.loads((P/'env-J.json').read_text());env['LEAN_PATH']=str(O)+':'+str(D.parent/'codex-pv-runjoin-20261026/runjoin32-lean/external');(D/'env-J.json').write_text(json.dumps(env,indent=2)+'\n');(D/'external-authority.json').write_text(json.dumps(ext))
(D/'cohort-preflight.json').write_text(json.dumps(dict(checked=len(checked),rows=checked,external_checked=len(ext),old_environment_sha256=sha(P/'env-J.json'),environment=env,mismatches=[]),indent=2)+'\n');print('cohort dependencies',len(checked),'external',len(ext))
