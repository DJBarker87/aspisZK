from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,n in [(58,'NHC_CustodyWindows'),(59,'NHC_MarkerAny'),(60,'NHC_HintsTailFrame')]:
 a=f'NHC_L{i:03}';r=subprocess.run([sys.executable,str(E/'NHC_run.py'),a,'lean',n],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,n,r.returncode,flush=True)
 if r.returncode:print((r.stdout+r.stderr)[-1200:]);sys.exit(r.returncode)
