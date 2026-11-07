from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(62,'NLQ_Stage1Result'),(63,'NLQ_SnapshotSkip'),(64,'NLQ_SnapshotEvents'),(65,'NLQ_ClosedSnapshotStep'),(66,'NLQ_ClosedThreeSnapshots'),(67,'NLM_DeployedOps')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',m],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else m+': no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
