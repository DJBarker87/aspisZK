"""Verify the frozen runjoin44 cohort and reuse it read-only under h6."""
from pathlib import Path
import json,lzma,subprocess,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028'
plan=json.loads((E/'build-plan.json').read_text())
x=json.loads(lzma.decompress((E/'reuse-expected.json.xz').read_bytes()))
x['plan']=plan
code=r'''
import pathlib,json,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['plan']['workspace'])
old=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin32-lean')
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert not p.exists(), 'private workspace already exists'
checks=[]
for v in x['projects']:
 m=v['module'];rel=m.replace('.','/');s=old/'sources'/(rel+'.lean');o=old/'objects'/(rel+'.olean')
 assert sha(s)==x['plan']['modules'][m]['sha256'],('source',m)
 assert sha(o)==v['expected_object_sha256'],('object',m)
 checks.append(dict(module=m,source_sha256=sha(s),object_sha256=sha(o)))
for v in x['dependencies']:
 q=pathlib.Path(v['path']);assert sha(q)==v['expected'],('dependency',v)
for v in x['external']:
 q=pathlib.Path(v['path']);assert sha(q)==v['expected'],('external',v)
for v in x['ir']:
 q=old/'external'/(v['module'].replace('.','/')+'.ir');assert sha(q)==v['expected'],('ir',v)
env=json.load(open(old/'J.json'));base=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
assert all(env[k]==base.get(k) for k in env if k!='LEAN_PATH')
assert env['LEAN_PATH']==str(old/'objects')+':'+str(old/'external')
p.mkdir();(p/'objects').mkdir();(p/'sources').mkdir();(p/'evidence').mkdir();(p/'source-history').mkdir()
# Preserve the original import search prefix exactly for the inherited cohort.
# New modules live only in the new job's prefix; no old object is written.
env['LEAN_PATH']=str(p/'objects')+':'+env['LEAN_PATH']
(p/'J.json').write_text(json.dumps(env));(p/'build-plan.json').write_text(json.dumps(x['plan']))
print(json.dumps(dict(all_match=True,projects=checks,dependencies=len(x['dependencies']),external=len(x['external']),ir=len(x['ir']),toolchain=env['LEAN_GITHASH'],inherited_prefix=str(old/'objects')+':'+str(old/'external'),LEAN_PATH=env['LEAN_PATH'],old_workspace_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(x),text=True,capture_output=True)
(E/'prepare-transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr))+'\n')
assert r.returncode==0,r.stderr
b=r.stdout.encode();(E/'reuse-verified.json.xz').write_bytes(lzma.compress(b));(E/'reuse-verified.json.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n')
print('Verified read-only reuse:',len(x['projects']),'projects,',len(x['external']),'external objects')
