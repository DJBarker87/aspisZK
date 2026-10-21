#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,sys,hashlib
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit17-20261021'
host='dombarker@100.108.41.90'
rows=[]
compact=(E/'rust-sources/compact-with-harness.rs').read_bytes()
for name in sys.argv[1:]:
 d=E/'receipts'/name;d.mkdir(exist_ok=True,parents=True)
 for f in ['receipt.json','stdout.log','stderr.log','time.log']:
  subprocess.run(['scp',host+':'+H+'/receipts/'+name+'/'+f,str(d/f)],check=True)
 subprocess.run(['scp',host+':'+H+'/'+name+'-inputs.json',str(E/(name+'-inputs.json'))],check=True)
 x=json.loads((d/'receipt.json').read_text());pins=json.loads((E/(name+'-inputs.json')).read_text())
 assert x['swaps']==0
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
 assert pins['source_hashes']['crates/aspis-r1-cost-probe/src/compact.rs']==hashlib.sha256(compact).hexdigest()
 x.update(name=name,accepted=x['exit_status']==0,source_revision=pins['source_revision'],source_hashes=pins['source_hashes'])
 if x['accepted']:assert 'VERIFICATION:- SUCCESSFUL' in (d/'stdout.log').read_text()
 rows.append(x)
(E/'rust-attempts.json').write_text(json.dumps(rows,indent=2)+'\n')
code="""import hashlib,json
from pathlib import Path
p=Path(%r)
rows=[dict(path=str(x.relative_to(p)),sha256=hashlib.sha256(x.read_bytes()).hexdigest(),bytes=x.stat().st_size) for x in sorted(p.rglob('*.out'))]
print(json.dumps(rows,indent=2))
"""%(H)
r=subprocess.run(['ssh',host,'python3 -'],input=code,text=True,check=True,capture_output=True)
(E/'kani-artifacts.json').write_text(r.stdout)
print([(x['name'],x['exit_status'],x['wall_seconds']) for x in rows])
