from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(66,'NLQ_ClosedThreeSnapshots'),(71,'NLQ_SnapshotSkip'),(72,'NLQ_SnapshotEvents'),(73,'NLQ_SnapshotData'),(74,'NLQ_WritebackFrame'),(75,'NLQ_DispatchState'),(76,'NLQ_DispatchAlgebra')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',m],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else m+': no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
