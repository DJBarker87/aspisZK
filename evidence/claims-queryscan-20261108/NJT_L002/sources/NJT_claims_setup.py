from pathlib import Path
import json,shutil,hashlib,subprocess
import NJT_stage as stage
B=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads/codex-cx-verify-observed7-20261108')
for n,h in json.loads((B/'NJT_PAYLOAD_PINS.json').read_text()).items():
 p=P/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 shutil.copyfile(p,B/n.replace('NJM_','NJT_'))
S=B/'NJT_src'
(B/'NJT_preflight').mkdir(exist_ok=True)
stage.stage(S);stage.validate(S,B/'NJT_preflight','/home/dombarker/.cargo/bin/cargo')
n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=S/n
original=p.read_text();ref=(B/'NJT_claims_ref.rs.txt').read_text()
p.write_text(original+'\n'+ref)
(B/'NJT_REFERENCE.patch').write_text('--- a/'+n+'\n+++ b/'+n+'\n@@ -'+str(len(original.splitlines()))+',0 +'+str(len(original.splitlines())+1)+','+str(len(ref.splitlines())+1)+' @@\n+\n'+''.join('+'+line+'\n' for line in ref.splitlines()))
(B/'NJT_REFERENCE_PINS.json').write_text(json.dumps(dict(frozen_source=hashlib.sha256(original.encode()).hexdigest(),reference=hashlib.sha256(ref.encode()).hexdigest(),scratch_source=hashlib.sha256(p.read_bytes()).hexdigest(),cargo_target_dir=str(B/'NJT_target')),indent=2))
print('NJM owned reference installed after frozen graph preflight')
