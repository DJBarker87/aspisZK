from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(54,'NLQ_Stage1State'),(55,'NLQ_CheckpointDomain'),(56,'NLQ_SnapshotThirdPrefix'),(57,'NLQ_CopyFrame'),(58,'NLQ_Stage1Ready'),(59,'NLQ_Stage1Cases')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',m],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else m+': no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
