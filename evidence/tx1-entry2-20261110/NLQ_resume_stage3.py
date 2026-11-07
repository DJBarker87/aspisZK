from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(49,'NLQ_Stage1State'),(51,'NLQ_CheckpointDomain'),(52,'NLQ_SnapshotThirdPrefix'),(53,'NLQ_SourceDispatch')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',m],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else m+': no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
