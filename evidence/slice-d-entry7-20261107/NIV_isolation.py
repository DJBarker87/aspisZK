"""Additional isolation gate, run before the unchanged historical native gate."""
from pathlib import Path
import json,os,sys,subprocess,hashlib
B=Path(__file__).resolve().parent
x=json.loads((B/sys.argv[1]).read_text());native=x['native_command']
target=native[native.index('--target-dir')+1]
assert Path(target)==B/'NIV_target'
assert os.environ['CARGO_TARGET_DIR']==target
assert Path(target).resolve().is_relative_to(B.resolve())
assert not (B/'NIV_target').is_symlink()
old=(B/x['original_config_file']).read_bytes()
assert hashlib.sha256(old).hexdigest()==x['original_config_sha256']
out=dict(allowed=True,explicit_target=target,environment_target=os.environ['CARGO_TARGET_DIR'],original_config_sha256=x['original_config_sha256'],relocated_config_sha256=hashlib.sha256((B/sys.argv[1]).read_bytes()).hexdigest(),old_target=x['old_target'])
(B/(x['attempt']+'-isolation.json')).write_text(json.dumps(out,indent=1)+'\n')
sys.exit(subprocess.run(x['historical_gate_command'],cwd=B).returncode)
