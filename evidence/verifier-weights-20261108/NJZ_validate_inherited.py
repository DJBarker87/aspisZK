"""Read-only validation of retained native windows; no theorem-count credit."""
from pathlib import Path
import json,hashlib,subprocess,lzma
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):
 f=R/p
 if f.is_file():return f.read_bytes()
 return subprocess.check_output(['git','show','HEAD:'+p])
def load(p):return json.loads(read(p))
selections={
'evidence/tx2-native6-20261108':[(5,6),(7,8),(26,27),(28,29),(30,31),(32,33),(34,35),(36,37),(17,18),(19,20),(21,22),(23,24),(70,71),(70,72),(70,73),(74,75),(76,77),(78,79),(11,12)],
'evidence/tx2-native7-20261108':[(39, 40), (39, 41), (37, 38), (37, 54), (37, 55), (49, 50), (49, 51), (42, 43), (42, 44), (42, 45)],
'evidence/tx2-native5-20261107':[(27,28),(33,34),(36,37)]}
records=[]
for base,pairs in selections.items():
 prefix={'evidence/tx2-native6-20261108':'NJJ','evidence/tx2-native7-20261108':'NJR','evidence/tx2-native5-20261107':'NJC'}[base]
 for pos,neg in pairs:
  pair=[]
  for n,positive in [(pos,True),(neg,False)]:
   a=f'{prefix}_K{n:03d}';p=f'{base}/{a}';r=load(p+'/receipt.json');out=read(p+'/stdout.log').decode();graph=load(f'{base}/{a}-graph-check.json');lock=load(f'{base}/{a}-lock-check.json');ad=load(f'{base}/{a}-admission.json')
   index={}
   for candidate in [f'{base}/{prefix}_INPUT_INDEX.json',f'{base}/{prefix}_INPUTS_INDEX.json']:
    attempt=subprocess.run(['git','show','HEAD:'+candidate],capture_output=True)
    if attempt.returncode==0:index=json.loads(attempt.stdout);break
   verified_inputs=[]
   for name,expected_hash in r['source_hashes'].items():
    capture=a+'/sources/'+name
    item=index.get(capture)
    if item:
     actual=lzma.decompress(read(base+'/'+item['archive'])) if 'archive' in item else read(base+'/'+item['file'])
     assert len(actual)==item['bytes'] and sha(actual)==item['sha256'],(a,name,'archive pin')
    else:actual=read(base+'/'+capture)
    assert sha(actual)==expected_hash,(a,name,'receipt source pin')
    if name.endswith('.rs') and any(z in name for z in ['parent','readers']):
     assert b'static mut' not in actual,(a,name,'writable static')
    verified_inputs.append(dict(name=name,sha256=expected_hash,bytes=len(actual)))
   assert (r['exit_status']==0)==positive,(a,r['exit_status'])
   assert 'timed out' not in out and 'VERIFICATION:- '+('SUCCESSFUL' if positive else 'FAILED') in out,a
   assert graph['graph_matches_frozen'] and lock['unchanged'],a
   assert lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
   assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
   assert r['env']['CARGO_NET_OFFLINE']=='true',a
   # The canonical KMX files were pinned by the retained validator, and its SHA
   # is in the same launcher receipt. Never substitute an own copy implementation.
   root=next(x for x in graph['all_crate_features'] if x['name']=='aspis-r1-cost-probe')
   assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(root['features']),(a,root)
   assert not any('static mut' in t for name,t in load(f'{base}/{prefix}_NATIVE_INPUTS.json').items() if name.endswith('.rs') and ('parent' in name or 'readers' in name)),a
   pair.append(dict(attempt=a,positive=positive,receipt=p+'/receipt.json',receipt_sha256=sha(read(p+'/receipt.json')),stdout_sha256=sha(out.encode()),graph_sha256=sha(read(f'{base}/{a}-graph-check.json')),lock_sha256=sha(read(f'{base}/{a}-lock-check.json')),source_hashes=r['source_hashes'],verified_inputs=verified_inputs,features=root['features'],CARGO_TARGET_DIR=r['env'].get('CARGO_TARGET_DIR'),kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'))
  records.append(pair)
(E/'NJZ_INHERITED_VALIDATION.json').write_text(json.dumps(dict(status='PASS',pairs=records,scope='Retained native cut evidence only; source/root composition and ledger gate separately required'),indent=2)+'\n')
print(f'Inherited validation PASS: {len(records)} exact positive/control pairs; no new native run.')
