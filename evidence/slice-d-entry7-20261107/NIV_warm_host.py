"""One authorized optimized Cargo dependency warm build; no extraction."""
from pathlib import Path
import json,hashlib,shutil,lzma,base64,subprocess,os,sys,time
B=Path(__file__).resolve().parent;S=B/'NIV_src';P=Path('/home/dombarker/project-offloads/codex-cx-extract-stage-20261106')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'NHR_STAGING_MANIFEST.json':'74a894c5ff7f4f3f3dda624b57891e6d7323fb2fa77c2b850d1c1ab4e3f18ad4','NHR_FROZEN_PAYLOAD.json.xz':'58902e9cc80f328a57a4348d6470075505388ff034bcceb36a27d1f4c38118c8','NHR_FROZEN_PAYLOAD.json.sha256':'89f8cf69f243878ff24cd659dc6b0269c013ff855af2902578a5e3a76bf9cb39'}
for n,h in pins.items():
 p=P/n;assert sha(p)==h
 q=B/n
 if q.exists():assert sha(q)==h
 else:shutil.copy2(p,q)
raw=lzma.decompress((B/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(B/'NHR_FROZEN_PAYLOAD.json.sha256').read_text().strip()
payload=json.loads(raw);manifest=json.loads((B/'NHR_STAGING_MANIFEST.json').read_text());changed=[]
for name,info in manifest['files'].items():
 data=base64.b64decode(payload[name]);assert hashlib.sha256(data).hexdigest()==info['sha256']
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==info['git_blob']
 p=S/name;assert p.resolve().is_relative_to(S.resolve());p.parent.mkdir(parents=True,exist_ok=True)
 if not p.exists() or p.read_bytes()!=data:
  changed.append(dict(path=name,before=sha(p) if p.exists() else None,after=info['sha256']));p.write_bytes(data)
old=B/'NIV_NHR_RESET.json'
if old.exists() and not (B/'NIV_NHR_RESET_FIRST.json').exists():shutil.copy2(old,B/'NIV_NHR_RESET_FIRST.json')
(B/'NIV_NHR_RESET.json').write_text(json.dumps(dict(reused_workspace=str(S),changed=changed,files=len(manifest['files']),duplicate_workspace_created=False),indent=1)+'\n')
import NIV_stage as stage
out=B/'NIV_warm';out.mkdir(exist_ok=True)
# Metadata uses the frozen stable Cargo; nightly-only codegen flags apply only to the build.
flags=os.environ.pop('RUSTFLAGS',None)
try:stage.validate(S,out,'/home/dombarker/.cargo/bin/cargo','entry')
finally:
 if flags is not None:os.environ['RUSTFLAGS']=flags
for name,h in stage.PINS.items():assert sha(stage.TOOLROOT/name)==h
assert not (B/'NIV_WARM_LAUNCHED.json').exists(),'Only ONE warm Cargo build authorized'
cmd=['/home/dombarker/.cargo/bin/cargo','+nightly-2026-09-17','build','--target-dir',str(B/'NIV_NHR_target'),'--manifest-path',str(S/'programs/r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','-j','4','--features','pool-adapter,private-leaf-salts']
assert os.environ['CARGO_TARGET_DIR']==str(B/'NIV_NHR_target')
version=subprocess.run(['/home/dombarker/.cargo/bin/rustc','+nightly-2026-09-17','--version','--verbose'],capture_output=True,text=True,check=True).stdout
before=sha(S/'Cargo.lock');record=dict(command=cmd,source_revision=stage.REV,cache=os.environ['CARGO_TARGET_DIR'],expected_time='optimized compilation of the frozen deployed program/dependencies only; no proof generation or elimination',inputs=pins,toolchain=version,lock_before=before)
(B/'NIV_WARM_LAUNCHED.json').write_text(json.dumps(record,indent=1)+'\n')
t=time.monotonic()
try:
 r=subprocess.run(cmd,cwd=S)
 record.update(exit=r.returncode,wall=time.monotonic()-t)
finally:
 record['lock_after']=sha(S/'Cargo.lock');record['lock_unchanged']=record['lock_after']==before
 record['source_unchanged']=all(sha(S/n)==i['sha256'] for n,i in manifest['files'].items())
 record['rlibs']=len(list((B/'NIV_NHR_target/release/deps').glob('*.rlib')))
 record['rmetas']=len(list((B/'NIV_NHR_target/release/deps').glob('*.rmeta')))
 (B/'NIV_WARM_RESULT.json').write_text(json.dumps(record,indent=1)+'\n')
 assert record['lock_unchanged'] and record['source_unchanged'],'STOP warm drift'
print(json.dumps({k:record[k] for k in ['exit','wall','rlibs','rmetas','lock_unchanged','source_unchanged']}),flush=True)
sys.exit(r.returncode)
