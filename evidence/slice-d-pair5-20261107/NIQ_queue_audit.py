from pathlib import Path
import subprocess,json,os
E=Path(__file__).resolve().parent
jobs=[(8,'lean','NIQ_COMBINED_IMPORT'),(9,'lean','NIQ_ProofDriver'),(10,'lean','NIQ_Driver'),(11,'linkaudit','NIQ_ProofDriver'),(12,'linkaudit','NIQ_Driver'),(13,'auditbin','fixtures')]
for i,kind,t in jobs:
 r=subprocess.run(['python3',str(E/'NIQ_run.py'),f'NIQ_L{i:03}',kind,t],env=dict(os.environ,NIQ_AUDIT='1'),capture_output=True,text=True)
 (E/f'NIQ_L{i:03}-queue.log').write_text(r.stdout+r.stderr)
 print(f'NIQ_L{i:03} {kind} exit{r.returncode}',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
r1=json.loads((E/'NIQ_L013/NIQ_ProofDriver_BINARY_PIN.json').read_text());r2=json.loads((E/'NIQ_L013/NIQ_Driver_BINARY_PIN.json').read_text())
(E/'NIQ_AUDIT_PINS.json').write_text(json.dumps(dict(proof=r1,scanner=r2,fixture_attempt='NIQ_L013'),indent=2)+'\n')
r=subprocess.run(['python3',str(E/'NIQ_run.py'),'NIQ_L014','auditbatch','NIQ_audit_batch'],capture_output=True,text=True)
(E/'NIQ_L014-queue.log').write_text(r.stdout+r.stderr)
print(f'NIQ_L014 auditbatch exit{r.returncode}',flush=True)
raise SystemExit(r.returncode)
