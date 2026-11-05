from pathlib import Path
import subprocess,json,os
E=Path(__file__).resolve().parent
jobs=[(23,'lean','NIG_COMBINED_IMPORT'),(24,'lean','NIG_ProofDriver'),(25,'lean','NIG_Driver'),(26,'linkaudit','NIG_ProofDriver'),(27,'linkaudit','NIG_Driver'),(28,'auditbin','fixtures')]
for i,kind,t in jobs:
 env=dict(os.environ,NIG_AUDIT='1')
 r=subprocess.run(['python3',str(E/'NIG_run.py'),f'NIG_L{i:03}',kind,t],env=env)
 if r.returncode:raise SystemExit('Review '+str(i))
r1=json.loads((E/'NIG_L028/NIG_ProofDriver_BINARY_PIN.json').read_text());r2=json.loads((E/'NIG_L028/NIG_Driver_BINARY_PIN.json').read_text())
(E/'NIG_AUDIT_PINS.json').write_text(json.dumps(dict(proof=r1,scanner=r2,fixture_attempt='NIG_L028'),indent=2)+'\n')
subprocess.run(['python3',str(E/'NIG_run.py'),'NIG_L029','auditbatch','NIG_audit_batch'],check=True)
