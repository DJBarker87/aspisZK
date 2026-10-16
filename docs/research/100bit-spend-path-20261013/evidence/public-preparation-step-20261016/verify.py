#!/usr/bin/env python3
"""Read/hash-only archive, exact Git cut, emitted bytes and producing receipts."""
from pathlib import Path, PurePosixPath
import hashlib,json,re,subprocess,tarfile
here=Path(__file__).resolve().parent;root=here.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
digest=lambda x:sha(json.dumps(x,sort_keys=True).encode())
m=json.loads((here/'manifest.json').read_text());p=here/m['archive']
assert sha(p.read_bytes())==m['archive_sha256'] and p.stat().st_size==m['archive_bytes']
with tarfile.open(p,'r:gz') as t:
 members=t.getmembers();assert len(members)==m['archive_entries']
 assert len({x.name for x in members})==len(members)
 for x in members:
  n=PurePosixPath(x.name);assert not n.is_absolute() and '..' not in n.parts
  assert x.isfile() or x.islnk()
  if x.islnk():assert x.linkname in t.getnames()
 data={x.name:t.extractfile(x).read() for x in members}
j=lambda n:json.loads(data[n])
entries={s.split('  ',1)[1]:s.split('  ',1)[0] for s in data['SHA256SUMS'].decode().splitlines()}
assert set(entries)==set(data)-{'SHA256SUMS'}
for n,h in entries.items():assert sha(data[n])==h,n
kit=root/'docs/research/100bit-spend-path-20261013/tools/public-preparation-extraction-kit'
pins=j('input/source-pins.json');assert pins['revision']==m['source_revision']
assert pins['features']==m['features']==['r0','private-leaf-salts']
sources={n:subprocess.check_output(['git','-C',str(root),'show',m['source_revision']+':'+n]) for n in pins['source_files']}
assert len(sources)==12 and len(pins['cuts'])==30
for n,b in sources.items():assert sha(b)==pins['source_files'][n]
for cut in pins['cuts']:
 b=sources[cut['path']][cut['start_byte']:cut['end_byte_exclusive']]
 assert sha(b)==cut['sha256'] and b==data['input/fragments/'+cut['name']+'.rs']
for n,h in pins['kit_files'].items():assert sha(data['input/'+n])==h and data['input/'+n]==(kit/n).read_bytes()
assert data['input/source-pins.json']==(kit/'source-pins.json').read_bytes()
for span in pins['layout_spans']:
 assert data['input/lib.rs'][span['start_byte']:span['end_byte_exclusive']]==data['input/fragments/'+span['name']+'.rs']
llbc=j('PublicPreparation.llbc');assert not llbc['has_errors']
assert llbc['translated']['files'][0]['contents'].encode()==data['input/lib.rs']
inventory=j('output-audit.json');assert inventory['llbc_sha256']==sha(data['PublicPreparation.llbc'])
assert len(inventory['actual_roots'])==4 and len(inventory['llbc_opaque_functions'])==43
assert len(inventory['emitted_function_inventory'])==36 and len(inventory['rust_file_inventory'])==66
assert not inventory['generated_external_templates'] and not inventory['generated_opaque_functions']
for n,h in inventory['emitted_files'].items():assert sha(data['generated/'+n])==h
for f in inventory['rust_file_inventory']:
 raw=llbc['translated']['files'][f['id']]['contents']
 assert (sha(raw.encode()) if raw is not None else None)==f['contents_sha256']
limits={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
for n,r in m['extraction_receipts'].items():
 assert r==j('runs/'+n+'/receipt.json') and r['exit_status']==0
 assert r['limits']==limits and r['process_swaps']==0 and r['cgroup_swap_current']==0
 assert r['source_pins_sha256']==sha(data['input/source-pins.json'])
 for path,h in r['outputs'].items():assert sha(data[path])==h
snapshot=j('proofs/external-inputs.json');keys={};visiting=set()
def key(n):
 if n in keys:return keys[n]
 assert n not in visiting;visiting.add(n);x=snapshot['modules'][n]
 keys[n]=digest({'source':x['source_sha256'],'objects':{s:o['sha256'] for s,o in x['objects'].items()},'imports':{d:key(d) for d in x['imports']},'runtime':snapshot['runtime_files']})
 visiting.remove(n);return keys[n]
reports=[]
for n,r in m['lean_receipts'].items():
 assert r==j('proofs/successful-targets/'+n+'.json')==j('proofs/runs/shared-a/'+n+'/receipt.json')
 assert r['exit_status']==0 and r['axioms']['passed'] and r['limits']==limits
 assert r['key']['options']==['-j1','-M0'] and r['key']['runtime']==snapshot['runtime_files']
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0' and not r['dependency_build'] and not r['backend_build']
 source=data['proofs/sources/'+n.replace('.','/')+'.lean']
 assert source==data['proofs/runs/shared-a/'+n+'/source.lean']==(root/r['source_manifest_entry']['source']).read_bytes()
 assert sha(source)==r['key']['source_sha256']
 for ext,o in r['objects'].items():assert sha(data['proofs/objects/'+n.replace('.','/')+ext])==o['sha256']
 if n.startswith('AspisR1PublicPreparation.'):
  assert source==data['generated/'+n.replace('.','/')+'.lean']
 for dep,k in r['key']['imports'].items():
  if dep in m['lean_receipts']:
   pr=m['lean_receipts'][dep];assert k=={'receipt_key':digest(pr['key']),'objects':pr['objects']}
  else:assert k=={'closure_key':key(dep),'objects':snapshot['modules'][dep]['objects']}
 log=data['proofs/runs/shared-a/'+n+'/lean.log'].decode()
 actual=[{'declaration':d,'axioms':[x.strip() for x in a.split(',') if x.strip()]} for d,a in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]",log,re.S)]
 assert actual==r['axioms']['reports'];reports.extend(actual)
assert len(reports)==10 and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
# Re-prove naming/body preservation against original producing Git blobs.
comparison=j('original-definition-comparison.json')
def strip(s):return re.sub(r"Source: 'lib.rs', lines [0-9:]+-[0-9:]+", "Source: 'lib.rs', lines PINNED_SEPARATELY",s)
for name in ['Types.lean','Funs.lean']:
 old=subprocess.check_output(['git','-C',str(root),'show','f6521c1249cef35b01b2e343445ec795d9ec82eb:docs/research/100bit-spend-path-20261013/lean/extracted-public-preparation-20261016/AspisR1PublicPreparation/'+name])
 raw=data['generated/AspisR1PublicPreparation/'+name];reduced=raw.decode();added=''
 if name=='Funs.lean':
  start=reduced.index('/-- [aspis_r1_public_preparation::r1_wire::{aspis_r1_public_preparation::r1_wire::SemanticTranscript<H>}::sample_block_validated]')
  end=reduced.index('/-- [aspis_r1_public_preparation::r1_semantic::public_transcript::',start)
  added=reduced[start:end];reduced=reduced[:start]+reduced[end:];assert added.count('\ndef ')==2
 assert strip(old.decode())==strip(reduced)
 c=comparison[name];assert c['old_sha256']==sha(old) and c['new_sha256']==sha(raw)
 assert c['common_normalized_sha256']==sha(strip(reduced).encode())
 assert c['added_declarations_sha256']==(sha(added.encode()) if added else None)
rootaudit=j('root-selection-audit.json');assert rootaudit['llbc_sha256']==sha(data['PublicPreparation.llbc'])
assert len(rootaudit['actual_step_and_wrapper_ids'])==2
for i in rootaudit['actual_step_and_wrapper_ids']:assert {'Fun':{'NonRec':i}} in llbc['translated']['ordered_decls']
assert data['pack.py']==(here/'pack.py').read_bytes()
print(f'PASS {len(members)} members; 30 exact cuts/12 Git files; 4 extended Lean targets/10 standard-only reports; original34 definitions preserved; 43 LLBC opaque entries retained')
