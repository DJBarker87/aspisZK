"""Read-only merged-delivery check before each Run6 stage."""
from pathlib import Path
import subprocess,json,hashlib,sys
E=Path(__file__).resolve().parent
row={'stage':sys.argv[1], 'research':subprocess.check_output(['git','rev-parse','research'],text=True).strip(),'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'handoffs':{}}
for name,path in [('a1','evidence/a1-20261108/NNV_HANDOFF.md'),('a2','evidence/a2-20261108/NNU_HANDOFF.md')]:
 r=subprocess.run(['git','show','research:'+path],capture_output=True)
 row['handoffs'][name]={'merged':r.returncode==0,'path':path,'sha256':hashlib.sha256(r.stdout).hexdigest() if r.returncode==0 else None}
 if r.returncode==0:(E/('NNH_Run6_'+name+'_merged.txt')).write_bytes(r.stdout)
row['sp.rest']='No assigned sibling or delivered rest field in run5b'
with (E/'NNH_Run6_LANDINGS.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
print(json.dumps(row))
