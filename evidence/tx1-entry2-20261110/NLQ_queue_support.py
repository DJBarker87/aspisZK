from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for i,name in [(5,'NLM_SnapshotBridge'),(6,'NLM_SnapshotState'),(7,'NLM_SnapshotAcquire'),(8,'NLM_SnapshotPrefix'),(9,'NLM_SnapshotReturn'),(10,'NLQ_RowSpec094')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',name],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else f'{name}: no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
