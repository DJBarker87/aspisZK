from pathlib import Path
import json,subprocess,sys
D=Path('/home/dombarker/project-offloads/codex-pv-skwb-20261029')
r=json.loads((D/'staging.json').read_text());todo=[]
for row in r['build']:
 p=D/'objects'/(row['module'].replace('.','/')+'.olean')
 # Existing objects were independently pinned and cohort-checked by full L1 h6.
 if p.is_file():continue
 todo.append(row)
(D/'remaining-plan.json').write_text(json.dumps(todo,indent=2)+'\n')
print('remaining exact pinned-source modules:',len(todo),flush=True)
# Retain two starts for the requested witness and single combined audit.
for n,row in zip(range(69101,69138),todo):
 rc=subprocess.run(['python3',str(D/'run.py'),'lean'+str(n),'lean',str(n),row['module']])
 if rc.returncode:sys.exit(rc.returncode)
