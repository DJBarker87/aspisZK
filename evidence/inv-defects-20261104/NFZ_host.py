"""Admission, immutable upload, one scope, read-only recovery. Never resubmit."""
import pathlib,subprocess,json,time,sys,hashlib,lzma
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1];H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-inv-defects-20261104';I='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
def ssh(code,data=None):
 for k in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
  with (E/'NFZ_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(command=code,retry=k,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if k==10:raise RuntimeError('persistent prelaunch transport failure')
  time.sleep(60)
attempt=sys.argv[1] if len(sys.argv)>1 else None
assert attempt in ['NFZ_B002','NFZ_B003','NFZ_B004'], 'part 2 permits only new attempt IDs'
for k in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
with (b/'{attempt}-barrier.log').open('w') as log:r=subprocess.run(['python3',{I!r}+'/JFz_reservation.py',str(b/'{attempt}-admission.json')],stdout=log,stderr=subprocess.STDOUT)
p=b/'{attempt}-admission.json'
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''');(E/f'{attempt}-admission-{k}.log').write_text(r.stdout+r.stderr)
 try:a=json.loads(r.stdout)
 except ValueError:
  if k==0:time.sleep(30);continue
  raise RuntimeError('Missing reservation JSON')
 (E/f'{attempt}-admission.json').write_text(json.dumps(dict(exit=r.returncode,reservation=a),indent=1))
 if r.returncode==0 and a.get('allowed') is True:break
 if r.returncode==78 or a.get('allowed') is False:
  if k==10:raise RuntimeError('Admission exhausted')
  print('Reservation refused; waiting',flush=True);time.sleep(180);continue
 raise RuntimeError(r.stdout+r.stderr)
files={p.name:p.read_text() for p in [E/'NFZ_check.py',E/'NFZ_rustc.py',E/'NFZ_SOURCE_PINS.json']}
payload=json.loads(lzma.decompress((E/'NFZ_FROZEN_SOURCE.json.xz').read_bytes()))
cfg=dict(attempt=attempt,kind='rust-typecheck',module=('independent frozen deployed MIR opt-level 0 vs 1 and typed HIR' if attempt=='NFZ_B003' else 'frozen deployed verifier MIR and typed HIR'),sources=['NFZ_check.py','NFZ_rustc.py','NFZ_SOURCE_PINS.json'],command=['python3','NFZ_check.py'],env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_INCREMENTAL='0',CARGO_PROFILE_DEV_DEBUG='0',RUSTC_WRAPPER=B+'/NFZ_rustc.py'),timeout=600,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_tree_dirty=True,expected_time='debug type-check compilation and MIR/typed-HIR diagnostic emission; no arithmetic gate, Kani, extraction or ELF')
files[f'{attempt}.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json,os
b=Path({B!r});files=json.loads({json.dumps(files)!r});source=json.loads({json.dumps(payload)!r})
assert not (b/'{attempt}').exists(),'attempt already submitted'
for n,t in files.items():(b/n).write_text(t)
for n,t in source.items():
 p=b/'NFZ_src'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
os.chmod(b/'NFZ_rustc.py',0o700)
(b/'S2W_run_host.py').write_bytes((Path({I!r})/'S2W_run_host.py').read_bytes())
''');assert r.returncode==0,r.stderr
# Submission is deliberately not inside retry helper.
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'cd '+B+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+attempt+'.json'],text=True,capture_output=True)
(E/f'{attempt}-launcher.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr,flush=True)
if r.returncode==255:
 print('Submitted; recovering read-only, no resubmission',flush=True);time.sleep(60)
r=ssh('python3',f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({B!r});paths=[p for p in b.glob('NFZ_*') if p.is_file()]+list((b/'{attempt}').rglob('*'))
out={{}}
for p in paths:
 if not p.is_file():continue
 rel=str(p.relative_to(b))
 if p.stat().st_size>1000000:
  data=p.read_bytes();out[rel+'.xz']=dict(base64=base64.b64encode(lzma.compress(data)).decode());out[rel+'.sha256']=dict(text=hashlib.sha256(data).hexdigest()+'\\n')
 else:out[rel]=dict(text=p.read_text())
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,o in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if 'text' in o:p.write_text(o['text'])
 else:
  import base64
  p.write_bytes(base64.b64decode(o['base64']))
assert (E/f'{attempt}/receipt.json').exists(),'receipt unresolved: never resubmit'
q=json.loads((E/f'{attempt}/receipt.json').read_text())
with (E/'NFZ_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(q)+'\n')
print(json.dumps({k:q[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']}))
