from pathlib import Path
import json,subprocess,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjq-20261029'
plan=json.loads((E/'build-plan.json').read_text())
code='''import pathlib,json,sys,os
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);old=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin32-lean')
(p/'objects').mkdir(exist_ok=True);(p/'sources').mkdir(exist_ok=True)
for m in x['modules']:
 rel=m.replace('.','/')+'.olean';q=old/'objects'/rel
 if q.is_file():
  dst=p/'objects'/rel;dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():dst.symlink_to(q)
if not (p/'external').exists():(p/'external').symlink_to(old/'external',target_is_directory=True)
env=json.load(open(old/'J.json'));env['LEAN_PATH']=str(p/'objects')+':'+str(p/'external');(p/'J.json').write_text(json.dumps(env));(p/'build-plan.json').write_text(json.dumps(x));print('read-only object links prepared; no old source copied or written')
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(plan),text=True,capture_output=True);print(r.stdout,r.stderr);assert r.returncode==0
