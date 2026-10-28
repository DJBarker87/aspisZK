"""Build each missing unchanged module once into the approved persistent cache."""
from pathlib import Path
import json,hashlib,subprocess,sys
E=Path(__file__).resolve().parent
missing=json.loads((E/'NBG_MISSING_TRANSITIVE4.json').read_text())
for i,row in enumerate(missing,56):
 p=Path(row['source']);row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest();row['revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();row['unchanged']=subprocess.run(['git','diff','--quiet','HEAD','--',str(p)]).returncode==0
 assert row['unchanged']
 a=f'NBG_L{i:03d}';row['attempt']=a
 (E/'NBG_TRANSITIVE4_PINNED.json').write_text(json.dumps(missing,indent=2)+'\n')
 r=subprocess.run([sys.executable,str(E/'NBG_build.py'),a,str(p),row['module']],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout);print(a,row['module'],'driver',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text());print('exit',rc['exit_status'],flush=True)
 if rc['exit_status']!=0:raise SystemExit('STOP changed dependency proof inputs require review')
