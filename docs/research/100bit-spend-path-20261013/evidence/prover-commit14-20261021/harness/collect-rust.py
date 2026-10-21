#!/usr/bin/env python3
"""Collect completed own host gates, excluding every nonzero result."""
from pathlib import Path
import subprocess,json,sys,hashlib
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit14-20261021'
host='dombarker@100.108.41.90:'
rows=[]
for name in sys.argv[1:]:
 dest=E/'receipts'/name;dest.mkdir(exist_ok=True,parents=True)
 for f in ['receipt.json','stdout.log','stderr.log','time.log']:
  subprocess.run(['scp',host+H+'/receipts/'+name+'/'+f,str(dest/f)],check=True)
 subprocess.run(['scp',host+H+'/'+name+'-inputs.json',str(E/(name+'-inputs.json'))],check=True)
 x=json.loads((dest/'receipt.json').read_text());pins=json.loads((E/(name+'-inputs.json')).read_text())
 assert x['swaps']==0
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
 x.update(name=name,accepted=x['exit_status']==0,source_revision=pins['source_revision'],source_hashes=pins['source_hashes'])
 if name.startswith('m31-iteration'):
  v=name.rsplit('-',1)[1];p=E/'rust-sources'/('m31-iteration-'+v+'.rs.txt')
  if not p.exists():p=E/'rust-sources/state_only_hiding.rs'
 else:p=E/'rust-sources/state_only_hiding.rs'
 assert hashlib.sha256(p.read_bytes()).hexdigest()==pins['source_hashes']['crates/aspis-prover/src/state_only_hiding.rs'],name
 assert hashlib.sha256((E/'rust-sources/prover_commit_reference.rs').read_bytes()).hexdigest()==pins['source_hashes']['crates/aspis-prover/src/prover_commit_reference.rs'],name
 rows.append(x)
(E/'rust-attempts.json').write_text(json.dumps(rows,indent=2)+'\n')
try:subprocess.run(['scp',host+H+'/m31-iteration-v2-stop.json',str(E/'m31-iteration-v2-stop.json')],check=True)
except subprocess.CalledProcessError:pass
print([(x['name'],x['exit_status'],x['wall_seconds']) for x in rows])
