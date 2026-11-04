from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(23,'NFW_Bind'),(24,'NFW_Transcript'),(25,'NFW_TranscriptDomain'),(26,'NFW_PreparedControl'),(27,'NFW_PreparedResults'),(28,'NFW_PreparedFields')]:
 r=subprocess.run([sys.executable,str(E/'NFW_run.py'),f'NFW_L{i:03}','lean',m],capture_output=True,text=True)
 (E/f'NFW_L{i:03}-queue.log').write_text(r.stdout+r.stderr)
 print(i,m,r.returncode,r.stdout[-1000:],flush=True)
 if r.returncode:sys.exit(r.returncode)
