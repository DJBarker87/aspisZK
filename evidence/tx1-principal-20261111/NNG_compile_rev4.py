"""NNG source configuration for existing capped single-module launcher."""
from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent
a,target=sys.argv[1:3]
assert a.startswith('NNG_L') and target.startswith('NNG_')
assert not (E/'NNG_CLIENT_ACTIVE').exists(),'Wait for the one active client'
env=json.loads((E/'NNG_REV4_ENV.json').read_text())
src='NNG_generated/'+target+'.lean';p=E/src;p.parent.mkdir(exist_ok=True);p.write_bytes((E/(target+'.lean')).read_bytes())
x=dict(attempt=a,kind='lean',module=target,sources=[src],command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNG_generated','-o','NNG_R4_objects/'+target+'.olean',src],timeout=180,env=env,expected_time='One new focused NNG proof against private rev4 dependencies')
(E/(a+'.json')).write_text(json.dumps(x,indent=1)+'\n')
raise SystemExit(subprocess.run([sys.executable,str(E/'NNG_run.py'),a]).returncode)
