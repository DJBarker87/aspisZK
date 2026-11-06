from pathlib import Path
import hashlib,json,shutil,subprocess,os
B=Path.cwd();deleted=[]
# Only stale solver files inside this job's TMPDIR; all Kani scopes have ended.
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in (B/'NLC_tmp').rglob(pattern):
  if p.is_file():deleted.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
size=sum(p.lstat().st_size for p in B.rglob('*') if p.is_file() or p.is_symlink());assert size<30_000_000_000,size
lock=hashlib.sha256((B/'NLC_src/Cargo.lock').read_bytes()).hexdigest();assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
tools=[]
for cmd in [['/home/dombarker/.cargo/bin/cargo-kani','kani','--version'],['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','--version']]:
 r=subprocess.run(cmd,text=True,capture_output=True);tools.append(dict(command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
(B/'NLC_HOST_FINAL.json').write_text(json.dumps(dict(own_logical_bytes=size,under_30GB=True,disk=shutil.disk_usage(B)._asdict(),lock_sha256=lock,removed_own_solver_files=deleted,cache_and_target_retained=True,tools=tools),indent=2));print('Own workspace under30GB; frozen lock unchanged; only own stale solver files cleaned')
