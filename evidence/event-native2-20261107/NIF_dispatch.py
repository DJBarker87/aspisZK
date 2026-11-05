from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
r=subprocess.run([sys.executable,str(E/'NIF_run.py'),*sys.argv[1:]],capture_output=True,text=True)
(E/(sys.argv[1]+'-client.log')).write_text(r.stdout+r.stderr)
lines=[x for x in r.stdout.splitlines() if x.startswith('{')]
print(lines[-1] if lines else sys.argv[1]+' client exit '+str(r.returncode)+'; details in committed client log',flush=True)
sys.exit(r.returncode)
