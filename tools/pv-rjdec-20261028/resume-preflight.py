"""Recheck inherited pins before consuming the retained cache."""
from pathlib import Path
import json,lzma,subprocess,hashlib,shlex
E=Path('evidence/pv-rjdec-20261028');x=json.loads(lzma.decompress((E/'reuse-expected.json.xz').read_bytes()));x['plan']=json.loads((E/'build-plan.json').read_text())
code=r'''import pathlib,json,sys,hashlib
x=json.load(sys.stdin);old=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin32-lean');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for v in x['projects']:
 m=v['module'];rel=m.replace('.','/');assert sha(old/'sources'/(rel+'.lean'))==x['plan']['modules'][m]['sha256'],m;assert sha(old/'objects'/(rel+'.olean'))==v['expected_object_sha256'],m
for v in x['dependencies']+x['external']:assert sha(pathlib.Path(v['path']))==v['expected'],v
for v in x['ir']:assert sha(old/'external'/(v['module'].replace('.','/')+'.ir'))==v['expected'],v
print(json.dumps(dict(all_match=True,projects=len(x['projects']),dependencies=len(x['dependencies']),external=len(x['external']),ir=len(x['ir']))))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(x),text=True,capture_output=True);assert r.returncode==0,r.stderr;(E/'resume-preflight.json').write_text(r.stdout);print(r.stdout)
