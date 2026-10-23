"""Inspect retained GOTO property identities; no verification is run."""
from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent
p=B/'kani-target/kani/x86_64-unknown-linux-gnu/debug/deps/s2w_native_wrappers-51155b8ff5000735__RNvCs9QfzRyMw605_19s2w_native_wrappers26S2W_snapshot_proof_account.out'
tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')
r=subprocess.run([str(tool),str(p),'--show-properties','--json-ui'],capture_output=True,text=True,check=True)
(B/'proof-properties.json').write_text(r.stdout)
props=[p for obj in json.loads(r.stdout) for p in obj.get('properties',[])]
selected=[p for p in props if p.get('sourceLocation',{}).get('file','').endswith('src/lib.rs') and p.get('class')=='assertion']
print(json.dumps({'goto':{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size},'cbmc_sha256':hashlib.sha256(tool.read_bytes()).hexdigest(),'property_count':len(props),'source_assertions':selected},indent=2))
