"""Own scratch-only cfg(kani) instrumentation; preserves every non-annotation byte."""
from pathlib import Path
import sys,importlib.util,json,zlib,base64,subprocess,time,hashlib
E=Path(__file__).resolve().parent;sys.argv=['ncc','none'];s=importlib.util.spec_from_file_location('ncc',E/'NCC_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NCC_CONTRACT_INSTALL')
full=(E/'NCC_fullframes.rs.txt').read_text();patch=(E/'NCC_getter_annotations.patch').read_text();payload=json.dumps(dict(source=full,patch=patch))
encoded=base64.b64encode(zlib.compress(payload.encode(),9)).decode()
code='''from pathlib import Path
import json,zlib,base64,subprocess,hashlib
b=Path(%r);x=json.loads(zlib.decompress(base64.b64decode(%r)));p=b/'NBU_src/crates/aspis-statement/src/pool_v1/verifier_registry.rs'
old=p.read_text();before=hashlib.sha256(old.encode()).hexdigest();original_hash='a96657c8c221b5ca68227e5f1f0af955ce5c32374f00dea1e3e9cb41a7c46942'
q=b/'NCC_getter_annotations.patch';q.write_text(x['patch'])
if 'kani::ensures' not in old:
 assert before==original_hash,('unexpected scratch source',before)
 r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(q)],cwd=b/'NBU_src',capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
new=p.read_text();stripped=''.join(l for l in new.splitlines(True) if '#[cfg_attr(kani, kani::' not in l)
assert hashlib.sha256(stripped.encode()).hexdigest()==original_hash,'non-annotation source changed'
assert new.count('#[cfg_attr(kani, kani::ensures')==6 and new.count('#[cfg_attr(kani, kani::requires(true))]')==6
h=b/'NBU_src/crates/aspis-statement/src/pool_v1/NCC_slots.rs';h.write_text(x['source'])
print(json.dumps(dict(before=before,after=hashlib.sha256(new.encode()).hexdigest(),non_annotation_source_sha256=original_hash,patch_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),module_sha256=hashlib.sha256(h.read_bytes()).hexdigest(),requires='true: full typed domains',prover_submitted=False)))
'''%(m.B,encoded)
for n in range(11):
 try:r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',m.H,'python3 -'],input=code,capture_output=True,text=True,timeout=90)
 except subprocess.TimeoutExpired:
  with (E/'NCC_INSTALL_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,actual_exit=None,timeout=90,prover_submitted=False))+'\n')
  if n<10:time.sleep(60);continue
  raise SystemExit('STOP install transport')
 with (E/'NCC_INSTALL_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,prover_submitted=False))+'\n')
 if r.returncode!=255:break
 if n<10:time.sleep(60)
assert r.returncode==0,r.stdout+r.stderr
(E/'NCC_CONTRACT_INSTALL.json').write_text(r.stdout);print(r.stdout)
