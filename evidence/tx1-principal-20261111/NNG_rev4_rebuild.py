"""Private dependency refresh for RSL revision 4; existing admission/launcher only."""
from pathlib import Path
import json,re,sys,subprocess,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx1-principal-20261111'
files={p.stem:p for p in Path('evidence/lib-20261111/LIB_dependency_inputs').glob('*.lean')}
for folder in ['evidence/top-assembly-20261107','evidence/libc-20261111','evidence/lib-20261111','evidence/rowspec-lead-20261107',str(E)]:
 files.update({p.stem:p for p in Path(folder).glob('*.lean')})
def deps(n):return re.findall(r'^import (?:all )?([\w.]+)',files[n].read_text(),re.M) if n in files else []
seen=set();order=[]
def visit(n):
 if n in seen:return
 seen.add(n)
 for d in deps(n):visit(d)
 if n in files:order.append(n)
for root in ['NNG_ConcreteCalls094','NNG_TotalParse094','NNG_EraseHead094','NNG_PrepareObservation094']:visit(root)
changed={'RSL_TX1_094','RSL_TX1_328','RSL_TX1_345'}
for n in order:
 if any(d in changed for d in deps(n)):changed.add(n)
plan=[dict(module=n,path=str(files[n]),sha256=hashlib.sha256(files[n].read_bytes()).hexdigest()) for n in order if n in changed]
(E/'NNG_REV4_REBUILD_PLAN.json').write_text(json.dumps(plan,indent=1)+'\n')
env=json.loads((E/'NNG_ENV.json').read_text())
env['LEAN_PATH']=B+'/NNG_R4_objects:'+B+'/NNG_F9_objects:'+env['LEAN_PATH']
(E/'NNG_REV4_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
if '--run' not in sys.argv:print('Private rev4 dependency refresh:',len(plan),'modules');sys.exit()
for i,row in enumerate(plan,693):
 a=f'NNG_L{i:03}';n=row['module']
 if (E/a/'receipt.json').exists():
  assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0,(a,n)
  continue
 src='NNG_rev4_inputs/'+n+'.lean';p=E/src;p.parent.mkdir(exist_ok=True);p.write_bytes(Path(row['path']).read_bytes())
 x=dict(attempt=a,kind='lean',module=n,sources=[src],command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNG_rev4_inputs','-o','NNG_R4_objects/'+n+'.olean',src],timeout=180,env=env,expected_time='Focused single private dependency rebuild because RSL revision4 changed imported domains')
 (E/(a+'.json')).write_text(json.dumps(x,indent=1)+'\n')
 print(a,n,flush=True)
 r=subprocess.run([sys.executable,str(E/'NNG_run.py'),a])
 if r.returncode:sys.exit(r.returncode)
