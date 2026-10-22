from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit30-20261022';host='dombarker@100.108.41.90'
for name in ['receipts','*-inputs.json','*-stop.json']:
 subprocess.run(['scp','-r',f'{host}:{H}/{name}',str(E)],check=True)
S=E/'rust-sources';S.mkdir(exist_ok=True)
for variant,folder in [('semantic','src'),('fields','src-fields'),('semantic-v1','snapshots/semantic30-row14-v1'),('fields-v1','snapshots/fields-v1'),('fields-v2','snapshots/fields-v2'),('semantic-v3','snapshots/semantic-v3'),('semantic-modular-v1','snapshots/semantic-modular-v1'),('fields-v3','snapshots/fields-v3'),('caller-v1','snapshots/caller-v1'),('caller-v2','snapshots/caller-v2'),('caller-v3','snapshots/caller-v3'),('caller-v4','snapshots/caller-v4')]:
 for name in ['r1_wire.rs','sim.rs']:
  path=f'{folder}/crates/aspis-r1-cost-probe/src/{name}' if folder.startswith('src') else f'{folder}/{name}'
  subprocess.run(['scp',f'{host}:{H}/{path}',str(S/(variant+'-'+name+'.txt'))],check=True)
# The duplicate-module diagnostic is reconstructed exactly from its retained
# first adapter and the corrected fuel adapter. It was never accepted.
v1=(S/'semantic-v1-r1_wire.rs.txt').read_text()
v2=v1+'\n'+(E/'harness/semantic-kani30.rs').read_text()
(S/'semantic-v2-r1_wire.rs.txt').write_text(v2)
rows=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 x=json.loads(p.read_text());x['name']=p.parent.name
 inp=json.loads((E/(p.parent.name+'-inputs.json')).read_text())
 x['source_revision']=inp['source_revision'];x['source_hashes']=inp['source_hashes']
 x['deps_fingerprint']=hashlib.sha256(json.dumps(inp['source_hashes'],sort_keys=True).encode()).hexdigest()
 x['peak_note']='GNU time may report only timeout parent RSS after termination; use cgroup_memory_peak_bytes for scope peak.'
 assert x['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 for name in ['r1_wire.rs','sim.rs']:
  want=inp['source_hashes']['crates/aspis-r1-cost-probe/src/'+name]
  matches=[str(q.relative_to(E)) for q in S.glob('*'+name+'.txt') if hashlib.sha256(q.read_bytes()).hexdigest()==want]
  assert matches,(p,name,want)
  x.setdefault('source_snapshots',{})[name]=matches
 rows.append(x)
(E/'rust-receipts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
print('Collected',len(rows),'receipts with exact source snapshots')
