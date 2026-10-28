from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for item in sys.argv[1:]:
 a,name=item.split(':',1)
 r=subprocess.run([sys.executable,str(E/'NCH_kani.py'),'NCH_K'+a,'verifier::candidate::NCH_candidate::'+name])
 if r.returncode:raise SystemExit(r.returncode)
