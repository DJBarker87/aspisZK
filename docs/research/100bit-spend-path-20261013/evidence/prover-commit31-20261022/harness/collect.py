from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit31-20261022';host='dombarker@100.108.41.90'
for name in ['receipts','*-inputs.json','*-stop.json','*-llbc.json']:
 subprocess.run(['scp','-r',f'{host}:{H}/{name}',str(E)],check=True)
S=E/'rust-sources';S.mkdir(exist_ok=True)
for variant,folder in [('v2','snapshots/v2'),('v3','snapshots/v3'),('v4','snapshots/v4'),('v6','snapshots/v6'),('current','src'),('leaves','src-leaves'),('cells','src-cells'),('constructed','src-constructed'),('recursive','src-recursive'),('bytes','src-bytes'),('indexed','src-indexed'),('capacity','src-capacity'),('fixed','src-fixed'),('literal','src-literal'),('summary','src-summary')]:
 for name in ['sim.rs','sim_owned31.rs']:
  path=f'{folder}/crates/aspis-r1-cost-probe/src/{name}' if folder.startswith('src') else f'{folder}/{name}'
  subprocess.run(['scp',f'{host}:{H}/{path}',str(S/(variant+'-'+name+'.txt'))],check=True)
# Exact first source before byte serializer changes. The original host harness
# predates wide_serialization, added only in the local harness revision.
first=subprocess.check_output(['git','show','09eee7bad:crates/aspis-r1-cost-probe/src/sim_owned31.rs'])
(S/'v1-sim_owned31.rs.txt').write_bytes(first)
h=(E/'harness/publication-kani31.rs').read_text().split('    #[kani::proof]\n    #[kani::unwind(12)]\n    fn wide_serialization()')[0]+'}\n'
base=subprocess.check_output(['git','show','09eee7bad:crates/aspis-r1-cost-probe/src/sim.rs'],text=True)
(S/'v1-sim.rs.txt').write_text(base+h)
rows=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 if p.parent.name.startswith('build-'):continue
 x=json.loads(p.read_text());x['name']=p.parent.name
 inp=json.loads((E/(p.parent.name+'-inputs.json')).read_text())
 x['source_revision']=inp['source_revision'];x['source_hashes']=inp['source_hashes']
 x['deps_fingerprint']=hashlib.sha256(json.dumps(inp['source_hashes'],sort_keys=True).encode()).hexdigest()
 x['peak_note']='GNU time reports only timeout parent after SIGTERM; scope peak is authoritative for stopped Kani jobs.'
 assert x['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 for name in ['sim.rs','sim_owned31.rs']:
  want=inp['source_hashes']['crates/aspis-r1-cost-probe/src/'+name]
  matches=[str(q.relative_to(E)) for q in S.glob('*'+name+'.txt') if hashlib.sha256(q.read_bytes()).hexdigest()==want]
  assert matches,(p,name,want)
  x.setdefault('source_snapshots',{})[name]=matches
 rows.append(x)
(E/'rust-receipts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
print('Collected',len(rows),'completed receipts with exact source snapshots')
