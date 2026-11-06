"""Additional isolation gate, run before the unchanged historical native gate."""
from pathlib import Path
import json,os,sys,subprocess,hashlib
B=Path(__file__).resolve().parent
x=json.loads((B/sys.argv[1]).read_text());native=x['native_command']
target=native[native.index('--target-dir')+1]
assert Path(target)==B/'NJH_target'
assert os.environ['CARGO_TARGET_DIR']==target
assert Path(target).resolve().is_relative_to(B.resolve())
assert not (B/'NJH_target').is_symlink()
old=(B/x['original_config_file']).read_bytes()
assert hashlib.sha256(old).hexdigest()==x['original_config_sha256']
# One scope at a time: only completed own-run solver scratch may remain here.
tmp=B/'NJH_tmp';removed=[]
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in tmp.rglob(pattern):
  if p.is_file() and p.resolve().is_relative_to(tmp.resolve()):
   removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
(B/(x['attempt']+'-solver-cleanup.json')).write_text(json.dumps(dict(removed=removed,bytes=sum(r['bytes'] for r in removed),scope='owned NJH_tmp only; no active preceding scope'),indent=1)+'\n')
tool=subprocess.run([native[0],'--version'],capture_output=True,text=True)
assert tool.returncode==0 and '0.67.0' in tool.stdout,('STOP pinned Kani version',tool.returncode,tool.stdout,tool.stderr)
(B/(x['attempt']+'-tool-pin.json')).write_text(json.dumps(dict(version=tool.stdout.strip(),binary=str(Path(native[0]).resolve()),sha256=hashlib.sha256(Path(native[0]).read_bytes()).hexdigest()),indent=1)+'\n')
out=dict(allowed=True,explicit_target=target,environment_target=os.environ['CARGO_TARGET_DIR'],original_config_sha256=x['original_config_sha256'],relocated_config_sha256=hashlib.sha256((B/sys.argv[1]).read_bytes()).hexdigest(),old_target=x['old_target'])
(B/(x['attempt']+'-isolation.json')).write_text(json.dumps(out,indent=1)+'\n')
sys.exit(subprocess.run(x['historical_gate_command'],cwd=B).returncode)
