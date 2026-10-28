"""Optimized compile of the boxed function-cost probe and optional fresh fixture CLI."""
from pathlib import Path
import subprocess,sys,os,json,hashlib,shutil
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');W=H/'candidate'
cmd=['cargo','build','--manifest-path',str(H/'function-cost/Cargo.toml'),'--release','--offline','--locked','-j','4']
r=subprocess.run(cmd)
if r.returncode:raise SystemExit(r.returncode)
if '--batch2f' in sys.argv:
 cmd=['cargo','build','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--example','prover_rw_gate','--features','optimized-terminal,r1p-check,ct-host-prover']
 r=subprocess.run(cmd,cwd=W/'src')
 if r.returncode:raise SystemExit(r.returncode)
 target=Path(os.environ['CARGO_TARGET_DIR']);(W/'bin').mkdir(exist_ok=True)
 src=target/'release/examples/prover_rw_gate';dst=W/'bin/prover_rw_gate';shutil.copy2(src,dst)
 pins={}
 for name,p in [('prover_rw_gate',dst),('pv-batch2-function-cost',target/'release/pv-batch2-function-cost')]:
  pins[name]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
 (H/'batch2f-binary-pins.json').write_text(json.dumps(dict(source_revision=(W/'source-revision.txt').read_text().strip(),binaries=pins),indent=2)+'\n')
 print(json.dumps(pins),flush=True)
