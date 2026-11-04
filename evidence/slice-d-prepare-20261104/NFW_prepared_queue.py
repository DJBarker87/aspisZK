from pathlib import Path
import subprocess,sys,os
E=Path(__file__).resolve().parent
jobs=[(28,0,True)]+[(29+2*(f-1)+n,f,bool(n)) for f in range(1,15) for n in range(2)]
for i,facet,invert in jobs:
 env=dict(os.environ)
 if invert:env['NFW_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NFW_run.py'),f'NFW_K{i:03}','kani',f'verifier::NFW_prepared::prepared_facet{facet}'],env=env,capture_output=True,text=True)
 (E/f'NFW_K{i:03}-queue.log').write_text(r.stdout+r.stderr)
 print(i,facet,r.returncode,r.stdout[:350],flush=True)
 # A negative timeout is NOT a matched failing control.
 p=E/f'NFW_K{i:03}/stdout.log';out=p.read_text() if p.exists() else ''
 if r.returncode!=int(invert) or 'timed out' in out.lower() or (invert and 'Failed Checks:' not in out):sys.exit(r.returncode or 2)
