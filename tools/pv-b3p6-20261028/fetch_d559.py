"""Collect completed existing scopes only; no launch or resubmission."""
from pathlib import Path
import subprocess,tarfile,json,hashlib,lzma
R=Path('evidence/pv-b3p6-20261028/resume18');host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-b3p6-20261028'
p=subprocess.Popen(['ssh',host,f'cd {H} && tar czf - -T {H}/resume18/D559-collect-paths.txt'],stdout=subprocess.PIPE)
with tarfile.open(fileobj=p.stdout,mode='r|gz')as archive:
 for member in archive:
  assert member.isfile(),member.name
  name=member.name.removeprefix('resume18/');assert '..'not in Path(name).parts and not name.startswith('/')
  dest=R/name;dest.parent.mkdir(parents=True,exist_ok=True);b=archive.extractfile(member).read()
  if len(b)>20*1024*1024:
   assert name.endswith(('.llbc','.json','.log')), 'unexpected large artifact'
   dest.with_name(dest.name+'.xz').write_bytes(lzma.compress(b,preset=6))
   dest.with_name(dest.name+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n')
  else:dest.write_bytes(b)
assert p.wait()==0
inv=json.loads((R/'D559-final-host-inventory.json').read_text());bad=[]
for name,h in inv['hashes'].items():
 q=R/name.removeprefix('resume18/')
 b=q.read_bytes() if q.exists() else lzma.decompress(q.with_name(q.name+'.xz').read_bytes())
 if hashlib.sha256(b).hexdigest()!=h:bad.append(name)
assert not bad,bad
print(json.dumps(dict(host_hashes_verified=len(inv['hashes']),lean=inv['lean_attempts'],extraction_new=inv['new_native_receipts'],kani_new=inv['new_kani'])))
