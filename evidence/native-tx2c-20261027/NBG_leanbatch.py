from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a,m in [('NBG_L019','NBG_Atomic')]:
 r=subprocess.run([sys.executable,str(E/'NBG_build.py'),a,'lean/'+m+'.lean',m],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout);print(a,'driver',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 print(json.loads((E/a/'receipt.json').read_text())['exit_status'],flush=True)
