from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
files=['crates/aspis-r1-cost-probe/src/sim.rs','crates/aspis-prover/src/state_only_entropy.rs']
base='28776b162';host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-prover-commit19-20261021'
rows=[]
for f in files:
 original=subprocess.check_output(['git','show',base+':'+f]);local=Path(f).read_bytes()
 assert local.startswith(original)
 if f.endswith('/sim.rs'):
  tail=local[len(original):].decode();assert '#[cfg(any(kani,aeneas_ref))]' in tail and 'pub mod owned19' in tail
 else:assert local==original
 code='from pathlib import Path;import json,hashlib;p=Path('+repr(H+'/src/'+f)+');s=p.read_bytes();print(json.dumps(dict(prefix=hashlib.sha256(s[:'+str(len(original))+']).hexdigest(),full=hashlib.sha256(s).hexdigest(),size=len(s))))'
 remote=json.loads(subprocess.check_output(['ssh',host,'python3 -c '+"'"+code.replace("'","'\\''")+"'"],text=True))
 assert remote['prefix']==hashlib.sha256(original).hexdigest()
 rows.append(dict(path=f,base_revision=base,production_prefix_sha256=remote['prefix'],production_prefix_bytes=len(original),local_sha256=hashlib.sha256(local).hexdigest(),host_sha256=remote['full'],host_bytes=remote['size'],production_prefix_identical=True,change='cfg-gated proof references only; no release binary rebuild or byte-equality claim'))
(E/'source-binding.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Production source prefixes match',base)
