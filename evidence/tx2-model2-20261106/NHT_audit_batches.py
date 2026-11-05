from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
assert len(json.loads((E/'NHT_AUDIT_ROOTS.json').read_text())['groups'])==7
for i in range(7):
 a=f'NHT_L{57+i:03d}'
 r=subprocess.run([sys.executable,str(E/'NHT_run.py'),a,'audit','batch'+str(i)],capture_output=True,text=True)
 print(json.dumps({'attempt':a,'exit':r.returncode,'tail':r.stdout[-500:],'stderr':r.stderr[-1000:]}),flush=True)
 if r.returncode:sys.exit(r.returncode)
