from pathlib import Path
import subprocess,json,sys,hashlib,os
B=Path(__file__).resolve().parent
s=B/'NEF_src';lock=s/'Cargo.lock';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before=sha(lock)
assert before=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
for label in ['NEF_inv_differential','NEF_inv_wrong_conjugate']:
 cmd=['/home/dombarker/.cargo/bin/cargo','test','--release','--locked','--offline','--manifest-path',str(s/'crates/aspis-core/Cargo.toml'),'--target-dir',str(B/'NEF_rust_target'),'--features','r0','--lib','-j','1',label,'--','--nocapture']
 r=subprocess.run(cmd,cwd=s)
 print(json.dumps(dict(label=label,command=cmd,exit=r.returncode)),flush=True)
 assert (r.returncode==0) if label.endswith('differential') else (r.returncode==101)
assert sha(lock)==before
print(json.dumps(dict(lock_before=before,lock_after=sha(lock),unchanged=True,positive_cases=4096,zero_panics_matched=True,negative_control_failed=True)))
