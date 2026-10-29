"""Local sequential transport/driver; never compiles locally or overlaps scopes."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).parent;H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-diag3-20261029'
module=sys.argv[1];start=int(sys.argv[2]);first=int(sys.argv[3]) if len(sys.argv)>3 else 0
p=json.loads((E/'proof-plans.json').read_text())[module]
for i in range(first,len(p['steps'])):
 n=start+i-first;assert n<64197
 s='\n'.join('import '+m for m in p['imports'])+'\n'+p['base']+'\n\n'+'\n\n'.join(p['steps'][:i+1])+'\nend PV_DIAG3\n'
 src=E/(module+'.lean');src.write_text(s)
 subprocess.run(['scp',str(src),H+':'+D+'/sources/'],check=True)
 r=subprocess.run(['ssh',H,'python3',D+'/run.py','lean'+str(n),'lean',str(n),module])
 subprocess.run(['scp',H+':'+D+'/lean'+str(n)+'-*',str(E)+'/'],check=True)
 subprocess.run(['scp',H+':'+D+'/admission-lean'+str(n)+'.*',str(E)+'/'],check=True)
 if r.returncode:sys.exit(r.returncode)
 print('STEP',module,i+1,'ID',n,flush=True)
