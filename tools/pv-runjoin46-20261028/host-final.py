"""Read-only final pinned-workspace/toolchain and own-scope inventory."""
from pathlib import Path
import json,subprocess,shlex,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin46-20261028';p=json.loads((E/'build-plan.json').read_text())
code='''import pathlib,json,subprocess,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);env=json.load(open(p/'J.json'))
uncompiled=[]
for m,v in x['modules'].items():
 o=p/'objects'/(m.replace('.','/')+'.olean')
 if not o.is_file():uncompiled.append(dict(module=m,source_path=v['path'],source_sha256=v['sha256']))
r=subprocess.run([env['LEAN'],'--version'],text=True,capture_output=True);assert r.returncode==0
s=subprocess.run(['systemctl','--user','list-units','--plain','--no-legend','--state=running','pv46-lean-*'],text=True,capture_output=True);assert s.returncode==0
assert not s.stdout.strip(),s.stdout
print(json.dumps(dict(workspace=str(p),lean_version=r.stdout.strip(),LEAN_GITHASH=env['LEAN_GITHASH'],LEAN_PATH=env['LEAN_PATH'],own_running_scopes=s.stdout,uncompiled_staged_modules=uncompiled)))'''
for retry in range(11):
 r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(p),text=True,capture_output=True)
 if r.returncode!=255:break
 (E/f'final-transport-{time.time_ns()}.json').write_text(json.dumps(dict(retry=retry,exit=255,stderr=r.stderr),indent=2)+'\n')
 if retry==10:raise RuntimeError('ten transport retries exhausted')
 time.sleep(60)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'toolchain-and-final-scopes.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'not-compiled-staged-modules.json').write_text(json.dumps([x['module'] for x in out['uncompiled_staged_modules']],indent=2)+'\n')
print('Lean',out['lean_version'],'; own running scopes: 0; uncompiled:',[x['module'] for x in out['uncompiled_staged_modules']])
