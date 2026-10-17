from pathlib import Path
import hashlib,json,tarfile
W=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();digest=lambda v:sha(json.dumps(v,sort_keys=True).encode());m=json.loads((W/'manifest.json').read_text());arc=W/m['archive'];assert sha(arc.read_bytes())==m['archive_sha256']
with tarfile.open(arc) as t:
 sums={line.split('  ',1)[1]:line.split('  ',1)[0] for line in t.extractfile('SHA256SUMS').read().decode().splitlines()};assert len(sums)+1==m['archive_entries'];blobs={}
 for n,h in sums.items():
  b=t.extractfile(n).read();assert sha(b)==h,n;blobs[n]=b
 rs=m['formal_receipts'];assert len(rs)==5;reports=0
 shared=W.parent.parent/'lean/bridge-tx1-e5c186ba3-20261016'
 common=json.loads((shared/'common-funs-audit.json').read_text());assert common['A_prepared_binding_pins_sha256']==sha((shared/'prepared-binding-pins.json').read_bytes())
 for n,r in rs.items():
  assert r==json.loads(blobs['proof/successful-targets/'+n+'.json']);assert r['exit_status']==0 and r['axioms']['passed'];assert r['process_swaps']==0 and r['cgroup_swap_current']=='0';assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
  s=r['source_manifest_entry'];assert sha(blobs['proof/sources/'+s['stage_as']])==s['source_sha256'];assert sha((shared/s['stage_as']).read_bytes())==s['source_sha256']
  for suf,pin in r['objects'].items():assert sha(blobs['proof/objects/'+n.replace('.','/')+suf])==pin['sha256']
  for dep,pin in r['key']['imports'].items():
   if dep in rs:assert pin['receipt_key']==digest(rs[dep]['key']) and pin['objects']==rs[dep]['objects'],(n,dep)
  for report in r['axioms']['reports']:assert set(report['axioms'])<={'propext','Classical.choice','Quot.sound'}
  reports+=len(r['axioms']['reports'])
 assert reports==18
 llbc=json.loads(blobs[m['additional_cone']['llbc']]);assert not llbc['has_errors']
 pins=json.loads(blobs[m['additional_cone']['source_pins']]);base='tx1-actual-accumulator/input/'
 for n,h in pins['kit_files'].items():assert sha(blobs[base+n])==h,n
 assert len(pins['cuts'])==30
 for c in pins['cuts']:
  b=blobs[base+'fragments/'+c['name']+'.rs'];assert sha(b)==c['sha256'];assert b in blobs[base+'lib.rs'],c['name']
 excluded=json.loads(blobs['proof/excluded-old-universe.json'])['removed'];external=json.loads(blobs['proof/external-inputs.json']);assert not(set(excluded)&set(external['modules']))
 assert 'AspisR1PublicPreparation.Types' not in external['modules']
 print(f'PASS {len(sums)} archive members, 5 coherent focused targets, 18 standard-only axiom reports, 30 exact source cuts')
