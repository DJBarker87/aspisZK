"""Final tool identity inventory, not a new native/ELF result."""
from pathlib import Path
import subprocess,json,hashlib,os,shutil
B=Path.cwd();T=Path(os.environ['LEAN_SYSROOT']);H=Path('/home/dombarker');commands=[[str(T/'bin/lean'),'--version'],[str(T/'bin/lake'),'--version'],[str(H/'.cargo/bin/cargo-kani'),'--version'],[str(H/'.cargo/bin/rustc'),'--version','--verbose']];versions=[]
for cmd in commands:
 r=subprocess.run(cmd,text=True,capture_output=True);versions.append(dict(command=cmd,exit_status=r.returncode,stdout=r.stdout,stderr=r.stderr));assert r.returncode==0
pins={}
paths=[T/'bin/lean',T/'bin/lake',H/'.cargo/bin/cargo-kani']
for n in ['kani-compiler','cbmc','goto-instrument','goto-cc','rustc']:
 p=H/'.kani/kani-0.67.0/bin'/n
 if p.is_file():paths.append(p)
for p in paths:
 with p.open('rb')as f:h=hashlib.file_digest(f,'sha256').hexdigest()
 pins[str(p)]=dict(realpath=str(p.resolve()),sha256=h,bytes=p.stat().st_size)
x=dict(versions=versions,binaries=pins,historical_caveat='Final installed-tool identity; per-run source/dependency/config receipts remain authoritative. No historical ELF remeasurement.',extraction_attempts=0)
(B/'NMB_TOOLS.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(tools=len(pins),version_commands=len(versions))))
