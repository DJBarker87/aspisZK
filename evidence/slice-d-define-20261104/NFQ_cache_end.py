from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import hashlib,json,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-define-20261104');C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-define-cache-20261104');out=C/'NFQ_exports_20261104'
pins={str(p.relative_to(out)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in out.rglob('*') if p.is_file()}
units=subprocess.run(['systemctl','--user','list-units','--type=scope','--state=running','--no-pager','--no-legend'],capture_output=True,text=True)
tools={}
for name in ['lean','lake']:
 p=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin')/name;tools[name]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
p=Path('/home/dombarker/.cargo/bin/cargo-kani');tools['cargo-kani']=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(dict(exports=str(out),export_objects=pins,retained_cache=str(C),cache_retained=True,build_targets_absent={n:not (B/n).exists() for n in ['NFQ_target','NFQ_ref_target','NFQ_scan_ref_target']},disk_current=shutil.disk_usage(B)._asdict(),tool_pins=tools,running_scopes_snapshot=units.stdout,prior_cleanup='Own three Rust targets removed only after all final receipts; objects copied into own cache, never deleted; source/receipts/LLBC/audit binaries retained. No shared or wallet/key path touched.')))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);assert x['export_objects'] and all(x['build_targets_absent'].values())
(E/'NFQ_CACHE_END.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(exports=x['exports'],objects=len(x['export_objects']),cache_retained=True,free_bytes=x['disk_current']['free'])))
