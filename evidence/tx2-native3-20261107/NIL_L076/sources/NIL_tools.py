from pathlib import Path
import hashlib,json,subprocess,os
B=Path.cwd();T=Path(os.environ['LEAN_SYSROOT']);paths=[B/'S2W_run_host.py',B/'S2W_lean_host.py',T/'bin/lean',T/'bin/lake',T/'bin/leanc',Path('/home/dombarker/.cargo/bin/cargo-kani')]
for root in [Path('/home/dombarker/.kani/kani-0.67.0/bin'),Path('/home/dombarker/.kani/kani-0.67.0/toolchain/bin')]:
 if root.exists():paths += [p for p in root.iterdir() if p.is_file()]
pins={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,resolved=str(p.resolve())) for p in paths if p.is_file()}
versions={}
for command in [['/home/dombarker/.cargo/bin/cargo-kani','--version'],[str(T/'bin/lean'),'--version']]:
 r=subprocess.run(command,capture_output=True,text=True);assert r.returncode==0,(command,r.stderr);versions[' '.join(command)]=r.stdout+r.stderr
(B/'NIL_TOOL_PINS.json').write_text(json.dumps(dict(pins=pins,versions=versions),indent=2)+'\n');print(json.dumps(dict(pins=len(pins),versions=versions)))
