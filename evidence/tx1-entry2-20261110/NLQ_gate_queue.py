from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NLQ_make_audit.py')],check=True)
groups=len(json.loads((E/'NLQ_AUDIT_ROOTS.json').read_text())['groups'])
assert 3<=groups<=4
jobs=[(16,'lean','NLQ_COMBINED_IMPORT'),(17,'lean','NLQ_Driver'),(23,'lean','NLQ_ProofDriver'),(24,'link','NLQ_Driver'),(28,'link','NLQ_ProofDriver'),(32,'audit','fixtures'),(137,'audit','scan'),(138,'audit','batch0-1'),(139,'audit','batch2'+('-3'if groups==4 else'')),(140,'audit','retention')]
for n,kind,target in jobs:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{n:03d}',kind,target],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1]if r.stdout.strip()else target+': no receipt',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
