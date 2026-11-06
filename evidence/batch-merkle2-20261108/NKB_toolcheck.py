from pathlib import Path
import subprocess,json,hashlib,os,shutil
E=Path.cwd()
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--version'];r=subprocess.run(cmd,capture_output=True,text=True);assert r.returncode==0 and '0.67.0' in r.stdout,(r.returncode,r.stdout,r.stderr)
paths=[Path('/home/dombarker/.cargo/bin/cargo-kani'),E/'S2W_run_host.py',Path('/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py')]
T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0');paths += [T/'bin/lean',T/'bin/lake',T/'bin/leanc']
obj=dict(command=cmd,version=r.stdout.strip(),stderr=r.stderr,tools=[dict(path=str(p),resolved=str(p.resolve()),bytes=p.stat().st_size,sha256=sha(p)) for p in paths],cargo_target=os.environ['CARGO_TARGET_DIR'],disk=dict(zip(['total','used','free'],shutil.disk_usage(E))))
(E/'NKB_TOOL_PINS.json').write_text(json.dumps(obj,indent=2)+'\n');print('NKB tool preflight PASS: pinned Kani0.67.0, launcher/tool hashes recorded')
