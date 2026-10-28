"""Read-only hash audit of copied and original objects plus retained ELF/tools."""
from pathlib import Path
import json,hashlib,time
B=Path('/home/dombarker/project-offloads/codex-cx-l188-cache-20261028')
x=json.loads((B/'NDJ_CACHE_PINS.json').read_text());start=time.monotonic();errors=[];checked={}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def check(p,h,size=None):
 if p in checked:return
 q=Path(p)
 if not q.is_file():errors.append(dict(path=p,error='missing'));return
 actual=sha(q);n=q.stat().st_size
 checked[p]=dict(sha256=actual,bytes=n)
 if actual!=h or (size is not None and size!=n):errors.append(dict(path=p,expected=h,actual=actual,expected_bytes=size,bytes=n))
for r in x['objects']:
 for a in r['artifacts']:
  for p in [a['path'],a['original']]:check(p,a['sha256'],a['bytes'])
 for p,k in [(r.get('source'),'source_sha256')]:
  if p:check(p,r[k])
elves=[('default','/home/dombarker/project-offloads/codex-cx-native-elfscope-20261028/NCR_B003/artifacts/aspis_r1_cost_probe_program.so','f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4'),('devnet','/home/dombarker/project-offloads/codex-cx-native-elfpins-20261028/NCY_B001/artifacts/aspis_r1_cost_probe_program.so','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299'),('pool','/home/dombarker/project-offloads/codex-cx-native-elfpins-20261028/NCY_B002/artifacts/aspis_pool.so','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')]
for mode,p,h in elves:check(p,h)
for p,h in [('/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52/bin/rustc','d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002'),('/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c')]:check(p,h)
for name,h in {'reservation_agg16.py':'d6d40da5e7cad196b15974eb96526f28073d20b2c24855303d69bc605ebcac0f','S2W_lean_host_agg16.py':'9b325ab05e4aea7c8a2c3499ccef5de11898fdcba38cb803fc6a85111ca3f1dd','S2W_run_host_agg16.py':'8165ccff93f7d9b6043f55bf641c30c95c5af0f86d28b6e1b1ffef3aa5ea7ff6'}.items():check(str(B/name),h)
for tool in ['lean','lake']:
 p='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/'+tool;check(p,sha(Path(p)))
out=dict(exit_status=int(bool(errors)),checked_files=len(checked),errors=errors,wall_seconds=time.monotonic()-start,elves=[dict(mode=m,path=p,sha256=h) for m,p,h in elves],checked=checked)
print(json.dumps(out));raise SystemExit(bool(errors))
