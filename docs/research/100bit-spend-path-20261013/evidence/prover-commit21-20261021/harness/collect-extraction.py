from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit21-20261021';host='dombarker@100.108.41.90'
for name,ns in [('sim-tail-owned-v1','AspisR1SimTail21'),('sim-tail-control-v1','AspisR1SimControl21')]:
 d=E/'extraction'/name;d.mkdir(parents=True,exist_ok=True)
 # Rejected templates remain inert .txt files, never imported or promoted.
 result=subprocess.check_output(['ssh',host,'ls '+H+'/extraction/generated-'+name+'/'+ns],text=True)
 for f in result.splitlines():
  if f.endswith('.lean'):subprocess.run(['scp',host+':'+H+'/extraction/generated-'+name+'/'+ns+'/'+f,str(d/(f+'.txt'))],check=True)
for name in ['transcript21-binding.json','control21-binding.json','sim-later-v1-llbc.json','sim-later-v2-llbc.json','sim-tail-owned-v1-llbc.json','sim-tail-control-v1-llbc.json','sim-tail-control-v2-llbc.json']:
 subprocess.run(['scp',host+':'+H+'/'+name,str(E/name)],check=True)
for f in ['transcript-owned21.rs','transcript-control21.rs','tail-control21.rs']:
 subprocess.run(['scp',host+':'+H+'/harness/'+f,str(E/'harness'/f)],check=True)
rows=[]
for f in ['sim.rs','r1_wire.rs','transcript.rs']:
 p=Path('crates/aspis-r1-cost-probe/src')/f
 original=p.read_bytes()
 code='from pathlib import Path;import json,hashlib;p=Path('+repr(H+'/src/'+str(p))+');s=p.read_bytes();print(json.dumps(dict(prefix_sha256=hashlib.sha256(s[:'+str(len(original))+']).hexdigest(),full_sha256=hashlib.sha256(s).hexdigest(),size_bytes=len(s))))'
 remote=json.loads(subprocess.check_output(['ssh',host,'python3 -'],input=code.encode()))
 sha=hashlib.sha256(original).hexdigest();assert remote['prefix_sha256']==sha,(f,remote,sha)
 rows.append(dict(file=str(p),production_sha256=sha,production_size_bytes=len(original),**remote))
(E/'source-prefix-binding.json').write_text(json.dumps(dict(base='ec5946193',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),files=rows,scope='Exact source prefixes retained; all additions host-only under cfg(kani/aeneas_ref); no shipped source modification'),indent=2)+'\n')
