from pathlib import Path
import json,shutil,hashlib,subprocess
import NJM_stage as stage
B=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads/codex-cx-verify-observed6-20261107')
for n,h in json.loads((B/'NJM_PAYLOAD_PINS.json').read_text()).items():
 p=P/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 shutil.copyfile(p,B/n.replace('NHR_','NJM_'))
S=B/'NJM_src'
(B/'NJM_preflight').mkdir(exist_ok=True)
stage.stage(S);stage.validate(S,B/'NJM_preflight','/home/dombarker/.cargo/bin/cargo')
n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=S/n
original=p.read_text();ref=(B/'NJM_claims_ref.rs.txt').read_text()
p.write_text(original+'\n'+ref)
(B/'NJM_REFERENCE.patch').write_text('--- a/'+n+'\n+++ b/'+n+'\n@@ -'+str(len(original.splitlines()))+',0 +'+str(len(original.splitlines())+1)+','+str(len(ref.splitlines())+1)+' @@\n+\n'+''.join('+'+line+'\n' for line in ref.splitlines()))
(B/'NJM_REFERENCE_PINS.json').write_text(json.dumps(dict(frozen_source=hashlib.sha256(original.encode()).hexdigest(),reference=hashlib.sha256(ref.encode()).hexdigest(),scratch_source=hashlib.sha256(p.read_bytes()).hexdigest(),cargo_target_dir=str(B/'NJM_target')),indent=2))
print('NJM owned reference installed after frozen graph preflight')
