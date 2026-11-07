from pathlib import Path
import json,sys,subprocess,shutil
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx1-principal-20261111'
a,target=sys.argv[1:3]
assert a.startswith('NNG_L') and target.startswith('NNG_')
env=json.loads((E/'NNG_ENV.json').read_text())
src='NNG_generated/'+target.replace('.','/')+'.lean'
p=E/src
if (E/(target+'.lean')).exists():
 p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(E/(target+'.lean'),p)
if not p.exists():
 q=E/(target+'.lean')
 if not q.exists():q=(E/'NNG_lean'/target.replace('.','/')).with_suffix('.lean')
 assert q.exists(),q
 p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,p)
x=dict(attempt=a,kind='lean',module=target,sources=[src],command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNG_generated','-o','NNG_objects/'+target.replace('.','/')+'.olean',src],timeout=180,env=env,expected_time='Focused new module elaboration; one module only')
(E/(a+'.json')).write_text(json.dumps(x,indent=1)+'\n')
raise SystemExit(subprocess.run([sys.executable,str(E/'NNG_run.py'),a]).returncode)
