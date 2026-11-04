from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent;H='/home/dombarker/project-offloads/codex-pv-k4trace-20261104'
for ident in sys.argv[1:]:
 assert ident.startswith('K935')
 q=E/'host'/ident;q.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['scp','-r','dombarker@100.108.41.90:'+H+'/'+ident+'/.',str(q)],capture_output=True,text=True)
 assert r.returncode==0,r.stderr
 print(ident,'collected')
