from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
jobs=json.loads((E/'NCD_RETARGET_PLAN.json').read_text());state={'NCD_R_JFr_TX2_Tails':True};i=5
for row in jobs:
 m=row['module']
 if m in state:continue
 if any(d.startswith('NCD_') and not state.get(d) for d in row['imports']):
  state[m]=False;print('BLOCKED predecessor',m,flush=True);continue
 a=f'NCD_L{i:03d}';i+=1
 r=subprocess.run([sys.executable,str(E/'NCD_build.py'),a,row['path'],m],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():print('STOP missing receipt',a,r.stdout+r.stderr,flush=True);break
 rc=json.loads(p.read_text());state[m]=rc['exit_status']==0
 print(a,m,rc['exit_status'],rc['wall_seconds'],flush=True)
 if not state[m]:print((E/a/'stdout.log').read_text()[-3000:],flush=True)
(E/'NCD_RETARGET_STATE.json').write_text(json.dumps(state,indent=2)+'\n')
