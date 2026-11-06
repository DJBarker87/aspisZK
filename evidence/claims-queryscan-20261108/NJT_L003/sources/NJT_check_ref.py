from pathlib import Path
import json,hashlib,subprocess,os
import NJT_stage as stage
B=Path(__file__).resolve().parent;S=B/'NJT_src';n='crates/aspis-r1-cost-probe/src/r1_semantic.rs'
p=S/n;data=p.read_bytes();pins=json.loads((B/'NJT_REFERENCE_PINS.json').read_text())
assert hashlib.sha256(data).hexdigest()==pins['scratch_source']
ref=(B/'NJT_claims_ref.rs.txt').read_bytes();original=data[:-(len(ref)+1)]
assert hashlib.sha256(original).hexdigest()==pins['frozen_source']
out=B/'NJT_refcheck';out.mkdir(exist_ok=True)
try:
 p.write_bytes(original);stage.validate(S,out,'/home/dombarker/.cargo/bin/cargo')
finally:p.write_bytes(data)
lock=hashlib.sha256((S/'Cargo.lock').read_bytes()).hexdigest()
cmd=['cargo','check','--release','--locked','--offline','--jobs','4','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--features',stage.FEATURES]
r=subprocess.run(cmd,cwd=S)
after=hashlib.sha256((S/'Cargo.lock').read_bytes()).hexdigest();assert lock==after
(B/'NJT_REFERENCE_CHECK.json').write_text(json.dumps(dict(command=cmd,exit=r.returncode,lock_before=lock,lock_after=after,cargo_target_dir=os.environ['CARGO_TARGET_DIR'],expected_time='optimized-profile dependency compilation/type-check only; no arithmetic gate'),indent=2))
raise SystemExit(r.returncode)
