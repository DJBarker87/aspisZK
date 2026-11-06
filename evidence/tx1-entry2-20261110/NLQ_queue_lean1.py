from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(14,'NLQ_SnapshotFold'),(15,'NLQ_EmissionGuard'),(16,'NLQ_FrozenStage1Owned'),(17,'NLQ_TraceOfPacket')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',m],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else m+': no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
