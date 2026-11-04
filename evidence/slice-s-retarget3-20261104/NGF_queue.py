"""Serial focused builds; stop the dependent queue on failure for inspection."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;p=json.loads((E/'NGF_PROVENANCE.json').read_text());done={}
for f in sorted(E.glob('NGF_L*/receipt.json')):
 r=json.loads(f.read_text())
 if r['kind']=='lean':done[r['module']]=r['exit_status']
for n in p['order']:
 if n in p['independent_emitted_reuse']:continue
 m=p['module_owner'][n]
 if done.get(m)==0:continue
 nums=[int(f.name[5:8]) for f in E.glob('NGF_L[0-9][0-9][0-9].json')];i=max(nums,default=0)+1
 if i>110:raise RuntimeError('budget exhausted')
 r=subprocess.run([sys.executable,str(E/'NGF_run.py'),f'NGF_L{i:03}','lean',m])
 if r.returncode:sys.exit(r.returncode)
