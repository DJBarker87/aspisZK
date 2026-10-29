from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');P=D.parent/'codex-pv-diag3-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=json.loads((D/'cohort-plan.json').read_text());old=json.loads((P/'resume-cache-preflight.json').read_text());rows=old['rows'];external=json.loads((P/'external-authority.json').read_text()); ext={r['module'].replace('/','.'):r for r in external}
# Restrict first build to V2 and its transitive dependencies, excluding both unrelated gaps.
pins=json.loads((P/'project-resolution.json').read_text())['modules'];needed=set()
def visit(m):
 if m in needed:return
 needed.add(m)
 r=pins.get(m)
 deps=r['imports'] if r else rows[m].get('record_dependencies',{})
 for dep in deps:visit(dep)
visit('R1Z.PrivacyR1HeadlineV2')
bad=[];checked=[]
for m in needed-{'R1Z.PrivacyR1HeadlineV2'}:
 r=rows[m];p=Path(r['path']);assert sha(p)==r['sha256'],m
 if m in pins:assert pins[m]['sha256']==r.get('source_sha256'),m
 for dep,d in r.get('record_dependencies',{}).items():assert d['sha256']==rows[dep]['sha256'],(m,dep)
 checked.append(r)
for r in external:assert sha(Path(r['path']))==r['object_sha256']
(D/'v2-dependency-preflight.json').write_text(json.dumps(dict(checked=checked,external_checked=len(external),environment_sha256=sha(P/'env-J.json'),mismatches=bad),indent=2)+'\n')
O=D/'objects';O.mkdir(exist_ok=True)
for m in needed-{'R1Z.PrivacyR1HeadlineV2'}:
 if m in ext:continue
 dst=O/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(rows[m]['path'])
for m in plan['affected']:
 s=D/'sources'/(m.replace('.','/')+'.lean');s.parent.mkdir(parents=True,exist_ok=True);s.write_bytes((D/'source-inputs'/(m+'.lean.txt')).read_bytes());assert sha(s)==plan['source_pins'][m]['sha256']
# No stale project fallback; only validated local links and pinned external objects.
env=json.loads((P/'env-J.json').read_text());env['LEAN_PATH']=str(O)+':'+str(D.parent/'codex-pv-runjoin-20261026/runjoin32-lean/external');(D/'env-J.json').write_text(json.dumps(env,indent=2)+'\n');(D/'external-authority.json').write_text(json.dumps(external))
print('V2 deps',len(checked),'external',len(external))
