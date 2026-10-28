"""Reconstruct exactly four cfg-only scratch edits; compare all frozen files."""
from pathlib import Path
import subprocess,difflib,tempfile,hashlib,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2h-20261028'
m=json.loads((E/'NBQ_SCRATCH_MANIFEST.json').read_text())
paths=['crates/aspis-r1-cost-probe/src/fast_pairing.rs','crates/aspis-r1-cost-probe/src/fast_dots.rs','crates/aspis-r1-cost-probe/src/weights.rs','programs/r1-cost-probe/src/lib.rs']
patches=['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch','NBQ_u06e.patch','NBQ_error.patch','NBQ_u07.patch','NBQ_cells.patch','NBQ_tail.patch']
expected=dict(m)
with tempfile.TemporaryDirectory(prefix='NBQ-sourcecheck-') as d:
 for p in paths:
  q=Path(d)/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(subprocess.check_output(['git','show','4bb3b3f5:'+p]))
 for p in patches:
  subprocess.run(['git','apply','-'],input=(E/p).read_text(),cwd=d,text=True,check=True)
 for p in paths:expected[p]=hashlib.sha256((Path(d)/p).read_bytes()).hexdigest()
local=[]
for p,h in m.items():
 q=Path(p)
 if not q.is_file() or hashlib.sha256(q.read_bytes()).hexdigest()!=h:local.append(p)
target_errors=[p for p in local if p.startswith(('crates/','programs/'))]
assert not target_errors,target_errors
inherited=[]
for p in local:
 now=Path(p).read_bytes();head=subprocess.check_output(['git','show','HEAD:'+p])
 assert now==head,('uncommitted non-target change',p)
 inherited.append(dict(path=p,frozen_sha256=m[p],inherited_head_sha256=hashlib.sha256(head).hexdigest()))
(E/'NBQ_REPOSITORY_SOURCE_CHECK.json').write_text(json.dumps(dict(checked=len(m),errors=target_errors,inherited_non_target_differences=inherited,frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',shipped_files_unchanged=True),indent=2)+'\n')
code=f'''from pathlib import Path
import hashlib,json
s=Path({B!r})/'NBQ_src';expected={expected!r}
errors=[p for p,h in expected.items() if not (s/p).is_file() or hashlib.sha256((s/p).read_bytes()).hexdigest()!=h]
print(json.dumps(dict(checked=len(expected),errors=errors,modified_cfg_only={paths!r},expected_modified_hashes={{p:expected[p] for p in {paths!r}}},lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest()),indent=2))
assert not errors
'''
for n in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
 with (E/'NBQ_SOURCE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if n<10:time.sleep(60)
 else:raise SystemExit('transport exhausted')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);assert x['lock_sha256']==hashlib.sha256(subprocess.check_output(['git','show','4bb3b3f5:Cargo.lock'])).hexdigest()
x['patch_chain']=[dict(path=p,sha256=hashlib.sha256((E/p).read_bytes()).hexdigest()) for p in patches]
(E/'NBQ_SOURCE_CHECK.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(checked=x['checked'],errors=x['errors'])))
