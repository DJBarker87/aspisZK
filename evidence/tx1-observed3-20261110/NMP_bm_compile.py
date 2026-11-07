"""Serial NMP emitted-route client; reuse the existing capped launcher."""
from pathlib import Path
import json,re,subprocess,sys
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx1-observed3-20261110'
a,target=sys.argv[1:3]
assert re.fullmatch(r'NMP_L\d{3}',a) and 81<=int(a[-3:])<=280
assert target.startswith('NMP_') and not (E/a/'receipt.json').exists()
env=json.loads((E/'NMP_L036.json').read_text())['env']
src='NMP_generated/'+target.replace('.','/')+'.lean'
p=E/src
if not p.exists():
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((E/(target+'.lean')).read_bytes())
command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMP_generated','-o','NMP_objects/'+target.replace('.','/')+'.olean',src]
x=dict(attempt=a,kind='lean',module=target,sources=[src],command=command,timeout=180,env=env,expected_time='Focused new emitted-route module elaboration; one module only')
(E/(a+'.json')).write_text(json.dumps(x,indent=1)+'\n')
r=subprocess.run([sys.executable,str(E/'NMP_run.py'),a]);raise SystemExit(r.returncode)
