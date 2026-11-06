from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(36,'NLQ_CopyTrace'),(37,'NLQ_Stage1Copy'),(38,'NLQ_FirstPacket'),(39,'NLQ_CopyCases'),(40,'NLQ_SnapshotLaterPrefixes')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',m],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else m+': no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
