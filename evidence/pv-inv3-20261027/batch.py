from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for m in json.loads(Path(sys.argv[1]).read_text()):
 r=subprocess.run([sys.executable,str(E/'compile.py'),m],capture_output=True,text=True)
 print(m,r.returncode,flush=True)
 if r.returncode:
  print(r.stdout[-6000:]+r.stderr,flush=True);sys.exit(r.returncode)
