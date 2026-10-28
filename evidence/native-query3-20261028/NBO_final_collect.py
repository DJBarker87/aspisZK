from NBO_host import *
import hashlib,fcntl,tarfile,io
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
# Read the frozen tree in one archive; no code or builds run here.
blob=subprocess.check_output(['git','archive',frozen,'crates','programs','Cargo.lock','Cargo.toml'])
manifest={}
with tarfile.open(fileobj=io.BytesIO(blob)) as tar:
 for x in tar:
  if x.isfile():manifest[x.name]=hashlib.sha256(tar.extractfile(x).read()).hexdigest()
(E/'NBO_FROZEN_SOURCE_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
subprocess.run(['git','diff','--exit-code',frozen,'--','crates','programs','Cargo.lock','Cargo.toml'],check=True,capture_output=True)
with (E/'NBO_SERIAL.lock').open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 payload=dict(manifest=manifest,cache_start=json.loads((E/'NBO_CACHE_START.json').read_text()),library=json.loads((E/'NBO_LIBRARY_PIN.json').read_text()))
 payload_path=E/'NBO_final_payload.json'
 payload_path.write_text(json.dumps(payload))
 for trial in range(11):
  transfer=subprocess.run(['scp','-o','ConnectTimeout=15',str(payload_path),H+':'+B+'/NBO_final_payload.json'],capture_output=True,text=True)
  if transfer.returncode!=255:break
  if trial<10:time.sleep(60)
 assert transfer.returncode==0,transfer.stderr
 r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r});data=json.loads((b/'NBO_final_payload.json').read_text())
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028')
end={{str(p):pin(p) for p in cache.rglob('*') if p.is_file()}}
changed=[p for p,v in data['cache_start'].items() if p not in end or end[p]['sha256']!=v['sha256']]
assert not changed,('imported cache changed',changed)
paths=[cache,Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')]
resolved={{}}
for old,v in data['library'].items():
 rel=Path(old).relative_to(paths[2]);found=next((p/rel for p in paths if (p/rel).is_file()),None)
 assert found is not None
 actual=pin(found);assert actual['sha256']==v['sha256'],('Aeneas resolution mismatch',old,str(found))
 resolved[str(rel)]={{'resolved':str(found),**actual}}
mismatches=[];normalized={{}}
for n,h in data['manifest'].items():
 p=b/'NBO_src'/n
 if not p.is_file():mismatches.append({{'path':n,'missing':True}});continue
 raw=p.read_bytes();actual=hashlib.sha256(raw).hexdigest()
 if actual==h:continue
 original=raw
 if n=='crates/aspis-r1-cost-probe/src/candidate.rs':
  raw=raw.replace(b'\\n#[cfg(kani)] #[path="NBF_query.rs"] mod NBF_query;\\n',b'')
  raw=raw.replace(b'\\n#[cfg(kani)] #[path="NBO_native.rs"] mod NBO_native;\\n',b'')
 elif n=='crates/aspis-r1-cost-probe/src/verifier.rs':
  raw=raw.replace(b'\\n#[cfg(kani)] #[path="NBF_harness.rs"] mod NBF_harness;\\n',b'')
 if hashlib.sha256(raw).hexdigest()!=h:mismatches.append({{'path':n,'sha256':actual,'normalized_sha256':hashlib.sha256(raw).hexdigest(),'expected':h,'tail':original[-250:].decode(errors='replace')}})
 else:normalized[n]={{'scratch_sha256':actual,'frozen_sha256':h,'qualification':'only inherited NBF and own NBO cfg(kani) registrations removed'}}
print(json.dumps(dict(cache_end=end,cache_imports_unchanged=True,Aeneas_resolved=resolved,frozen_files=len(data['manifest']),scratch_mismatches=mismatches,scratch_normalized=normalized,cache_retained=str(cache))))
''')
 assert r.returncode==0,r.stderr
 out=json.loads(r.stdout)
 (E/'NBO_FINAL_HOST.json').write_text(json.dumps(out,indent=2)+'\n')
 assert not out['scratch_mismatches'],out['scratch_mismatches']
 print('Validated',out['frozen_files'],'frozen source files;',len(out['cache_end']),'retained cache files;',len(out['Aeneas_resolved']),'resolved Aeneas objects')
