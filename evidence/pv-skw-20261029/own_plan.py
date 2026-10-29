from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-skw-20261029');P=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows={r['module'].replace('/','.'):r for r in json.loads((D/'pins.json').read_text())['own']}
old=P/'codex-pv-ownn-20261029';env=json.loads((old/'env-J.json').read_text());paths=[P/'codex-pv-ownh-20261029/lean-objects',P/'codex-pv-ownd-20261029/lean-objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
# ownn cache is gone. Reuse only objects whose complete recorded import cohort matches.
planned=[];reused={};seen=set()
def select(m):
 return next((p/(m.replace('.','/')+'.olean') for p in paths if (p/(m.replace('.','/')+'.olean')).exists()),None)
def visit(m):
 if m in seen:return
 seen.add(m)
 if m not in rows:
  assert select(m),('unresolved',m);return
 r=rows[m]
 for dep in r['dependency_objects']:visit(dep)
 obj=select(m)
 match=obj and sha(obj)==r['object_sha256']
 if match:
  match=all((select(dep) and sha(select(dep))==h) for dep,h in r['dependency_objects'].items())
 if match:reused[m]=dict(r,selected=str(obj));return
 src=old/'lean-sources'/(m.replace('.','/')+'.lean')
 if not src.exists():src=P/'codex-pv-ownc-20261029/lean-sources'/(m.replace('.','/')+'.lean')
 assert src.exists() and sha(src)==r['source_sha256'],('source mismatch',m,str(src))
 planned.append(dict(r,module=m,source=str(src)))
visit('R1Z.PV_OWNN_SourceDense')
(D/'own-plan.json').write_text(json.dumps(dict(reused=reused,build=planned),indent=2)+'\n')
print('reuse',len(reused),'build',len(planned));print([r['module'] for r in planned])
