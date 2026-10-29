"""Final source/byte binding and safe cache cleanup; retains every key candidate."""
from pathlib import Path
import hashlib,json,os,shutil,stat
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected=json.loads((H/'final-expected-sources.json').read_text());bad=[dict(path=p,expected=h,actual=sha(H/'src'/p) if (H/'src'/p).is_file() else None) for p,h in expected.items() if not (H/'src'/p).is_file() or sha(H/'src'/p)!=h];assert not bad,bad
pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
elfs=[]
for mode,pin in pins.items():
 p=H/('elf-'+mode)/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so');assert sha(p)==pin
 ref=Path('/home/dombarker/project-offloads/codex-pv-client-20261026/artifacts')/(mode+'.so')
 row=dict(mode=mode,sha256=pin,bytes=p.stat().st_size,reference=str(ref))
 if ref.exists():
  assert sha(ref)==pin;row['literal_byte_comparison']=p.read_bytes()==ref.read_bytes();assert row['literal_byte_comparison']
 else:row['reference_missing']=True
 elfs.append(row)
assert sha(H/'native-target/client/devnet_spend')=='05673e4da06b3dbcf9890eb3737011375ce2a5a0f1a7f58e36179910f630a833'
assert json.loads((H/'corpus-ledger-audit.json').read_text())['passed']
A=H/'artifacts';A.mkdir(mode=0o700,exist_ok=False);artifacts=[]
for label,p in [('devnet_spend',H/'native-target/client/devnet_spend'),('baseline-devnet_spend',H/'native-target/release/devnet_spend'),('pv-c474-differential',H/'native-target/client/pv-c474-differential'),('pv-c474-fixture',H/'native-target/client/pv-c474-fixture'),('pv_client_gate',H/'native-target/release/pv_client_gate')]:
 q=A/label;shutil.copy2(p,q);artifacts.append(dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size))
# Retain all runtime/build key files. No private contents are exported.
keys=[]
for folder in [H/'runtime-private',H/'runtime-private-final',*(H/('elf-'+m) for m in pins)]:
 for p in folder.rglob('*'):
  if p.is_file() and (p.suffix=='.key' or p.name.endswith('keypair.json')):
   p.chmod(0o600);keys.append(dict(path=str(p),mode=oct(stat.S_IMODE(p.stat().st_mode)),bytes=p.stat().st_size,disposition='retained; no balance/authority cleanup performed'))
cleanup=[]
for name in ['native-target','probe-target','sbf-target-pool','sbf-target-verifier']:
 p=H/name;assert p.parent==H and not p.is_symlink()
 candidates=[]
 for f in p.rglob('*'):
  if not f.is_file():continue
  if f.suffix in ['.key','.pem']:candidates.append(str(f));continue
  if f.suffix=='.json':
   try:v=json.loads(f.read_text())
   except (ValueError,UnicodeDecodeError):v=None
   if isinstance(v,list) and len(v) in (32,64) and all(isinstance(n,int) and 0<=n<256 for n in v):candidates.append(str(f))
 if candidates:
  p.chmod(0o700)
  for candidate in candidates:Path(candidate).chmod(0o600)
  cleanup.append(dict(path=str(p),removed=False,reason='key candidates retained securely; no key cleanup authorized',candidates=candidates))
 else:shutil.rmtree(p);cleanup.append(dict(path=str(p),removed=True,reason='rebuildable cache only; no key candidates'))
r=dict(source_files_checked=len(expected),source_mismatches=bad,elfs=elfs,retained_artifacts=artifacts,retained_keys=keys,cache_cleanup=cleanup,release_pins_changed=False,keys_deleted=0,print_axioms='N/A; no Lean/Kani work')
(H/'final-audit.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='retained_keys'},indent=2),flush=True)
