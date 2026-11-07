from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(47,'NLQ_SnapshotThirdPrefix'),(48,'NLQ_FirstState'),(49,'NLQ_Stage1State')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',m],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else m+': no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
