from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for positive,negative in json.loads((E/sys.argv[1]).read_text()):
 r=subprocess.run([sys.executable,str(E/'NKR_run.py'),positive])
 if r.returncode:print(negative+' not launched; positive needs diagnosis',flush=True);continue
 subprocess.run([sys.executable,str(E/'NKR_run.py'),negative])
