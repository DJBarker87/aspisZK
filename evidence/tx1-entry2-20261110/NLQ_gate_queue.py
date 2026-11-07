from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(94,'lean','NLQ_OwnedGuard'),(123,'lean','NLQ_COMBINED_IMPORT'),(124,'lean','NLQ_Driver'),(125,'lean','NLQ_ProofDriver'),(126,'link','NLQ_Driver'),(127,'link','NLQ_ProofDriver'),(128,'audit','fixtures'),(129,'audit','scan')]
jobs.append((130,'audit','batch0-1'))
jobs.append((131,'audit','batch2-3'))
jobs.append((132,'audit','batch4-5'))
jobs.append((133,'audit','batch6-7'))
jobs.append((134,'audit','batch8-9'))
jobs.append((135,'audit','batch10-11'))
jobs.append((136,'audit','batch12-13'))
jobs.append((137,'audit','batch14-15'))
jobs.append((138,'audit','batch16-17'))
jobs.append((139,'audit','batch18-19'))
jobs.append((140,'audit','batch20-21'))
jobs.append((16,'audit','batch22-23'))
jobs.append((17,'audit','batch24-25'))
jobs.append((23,'audit','batch26-27'))
jobs.append((24,'audit','batch28-29'))
jobs.append((28,'audit','batch30'))
jobs.append((32,'audit','retention'))
for i,kind,target in jobs:
 if target=='NLQ_COMBINED_IMPORT':
  subprocess.run([sys.executable,str(E/'NLQ_make_audit.py')],check=True)
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}',kind,target],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else target+': no receipt',flush=True)
 if r.returncode:
  print('STOP: retain failure, inspect before further submissions',flush=True)
  raise SystemExit(r.returncode)
