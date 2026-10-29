"""Restore missing predecessors from their recorded authority blobs, privately."""
from pathlib import Path
import subprocess,json,hashlib,sys,tempfile
D=Path('evidence/pv-b3p6-20261028');H='/home/dombarker/project-offloads/codex-pv-b3p6-20261028';authority=json.loads((D/'resume8/project-resolution-resume8.json').read_text());mods=sys.argv[1:]
for m in mods:
 r=authority['modules'][m];raw=subprocess.check_output(['git','show',r['blob']]);assert hashlib.sha256(raw).hexdigest()==r['sha256'],m
 with tempfile.NamedTemporaryFile() as f:
  f.write(raw);f.flush();p=m.replace('.','/')+'.lean'
  subprocess.run(['ssh','dombarker@100.108.41.90','mkdir -p '+H+'/lean/'+str(Path(p).parent)],check=True)
  subprocess.run(['scp',f.name,'dombarker@100.108.41.90:'+H+'/lean/'+p],check=True)
subprocess.run(['scp',str(D/'resume8/project-resolution-resume8.json'),'dombarker@100.108.41.90:'+H+'/'],check=True)
subprocess.run(['ssh','dombarker@100.108.41.90','cd '+H+' && python3 continue_resume8_host.py modules '+' '.join(mods)],check=True)
