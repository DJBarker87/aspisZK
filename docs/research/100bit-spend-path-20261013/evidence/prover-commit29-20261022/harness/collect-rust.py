from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent.parent
host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022'
for folder in ['receipts','monitor']:
 subprocess.run(['scp','-r',host+':'+H+'/'+folder,str(E)],check=True)
for glob in ['*-inputs.json','kani-binding.json','frozen-elf-final-check.json']:
 subprocess.run(['scp',host+':'+H+'/'+glob,str(E)],check=True)
S=E/'rust-sources';S.mkdir(exist_ok=True)
for name in ['sim.rs','r1_wire.rs']:
 subprocess.run(['scp',host+':'+H+'/src/crates/aspis-r1-cost-probe/src/'+name,str(S/(name+'.txt'))],check=True)
# No production code changed in the proof workspace: only these two explicit
# cfg-only adapters are appended to exactly the final tracked native sources.
base=Path('crates/aspis-r1-cost-probe/src')
cut={'sim.rs':'#[cfg(kani)]\nmod step_kani29','r1_wire.rs':'\n#[cfg(kani)] pub fn make_kani29'}
identity={}
for name,marker in cut.items():
 raw=(S/(name+'.txt')).read_text();prefix=raw[:raw.index(marker)]
 assert prefix.rstrip()==(base/name).read_text().rstrip(),name
 identity[name]=dict(instrumented_sha256=hashlib.sha256(raw.encode()).hexdigest(),tracked_sha256=hashlib.sha256((base/name).read_bytes()).hexdigest(),native_prefix_unchanged=True)
x=json.loads((E/'host-proof-source-inventory.json').read_text())
assert {p['path'] for p in x['differences']}=={str(base/n) for n in cut}
for name in ['iteration29-row2-root-v1','iteration29-row0-empty-v2']:
 inp=json.loads((E/(name+'-inputs.json')).read_text())
 for f in ['sim.rs','r1_wire.rs']:
  want=inp['source_hashes'][str(base/f)];current=(S/(f+'.txt')).read_text()
  saved=S/(name+'-'+f+'.txt')
  if saved.exists() and hashlib.sha256(saved.read_bytes()).hexdigest()==want:continue
  if hashlib.sha256(current.encode()).hexdigest()==want:
   (S/(name+'-'+f+'.txt')).write_text(current);continue
  # The older empty-record run predates only the extra root-record harness.
  candidate=re.sub(r'^    #\[kani::proof\].*fn root_record\(\)\{check::<37,2>\(\)\}\n','',current,flags=re.M)
  pre,post=candidate.split(cut[f],1)
  found=None
  for n in range(1,20):
   value=pre.rstrip()+'\n'*n+cut[f]+post
   if hashlib.sha256(value.encode()).hexdigest()==want:found=value;break
  assert found is not None,(name,f,want)
  (S/(name+'-'+f+'.txt')).write_text(found)
(E/'proof-source-binding.json').write_text(json.dumps(dict(shipped_source_commit='a40439db1',identity=identity,checked_other_tracked_files=490,proof_only_adapters=['SemanticTranscript arbitrary-state factory','one iteration Kani harness and common sampler congruence summary'],scope='accepted root/empty preflights have exact source snapshots; no unproved field-bearing check is accepted'),indent=2)+'\n')
rows=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 x=json.loads(p.read_text());x['name']=p.parent.name
 assert x['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},p
 assert x['swaps']==0,p
 rows.append(x)
(E/'rust-receipts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
print('collected',len(rows),'completed receipts; exact native prefixes preserved')
