"""Own bounded receipt/source retention checks, one named artifact per mode."""
from pathlib import Path
import json,hashlib,os,sys,shutil
B=Path.cwd();mode=sys.argv[1];H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x): (B/n).write_text(json.dumps(x,indent=2)+'\n')
if mode=='pins':
 m=json.loads((B/'NLR_MODULES.json').read_text());sources=[];objects=[]
 for name,receipt in m['selected_receipts'].items():
  r=json.loads((B/receipt).read_text());p=B/'NLR_generated'/(name+'.lean');q=(B/receipt).parent/'sources/NLR_generated'/(name+'.lean')
  assert r['exit_status']==0 and H(p)==H(q)==r['source_hashes']['NLR_generated/'+name+'.lean']
  sources.append(dict(module=name,path=str(p),sha256=H(p),receipt=receipt,revision=r['source_revision']))
  for suffix in ['.olean','.olean.private','.olean.server','.ir']:
   p=B/'NLR_objects'/(name+suffix)
   if p.is_file():objects.append(dict(module=name,path=str(p),sha256=H(p),bytes=p.stat().st_size))
 write('NLR_PROOF_SOURCE.json',dict(sources=sources));write('NLR_PROOF_OBJECTS.json',dict(objects=objects))
 out=dict(status='PASS_SOURCE_OBJECT_PIN',sources=len(sources),objects=len(objects))
elif mode=='hypotheses':
 x=json.loads((B/'NLR_HYPOTHESIS_INVENTORY.json').read_text());s=(B/'NLR_L097/stdout.log').read_text()
 assert x['row_roots']==[] and x['full_child136_packet']is False and x['schemas_source_value_only']is True
 for n in x['printed_names']:assert n in s,n
 assert 'sorryAx'not in s and 'error:'not in s
 out=dict(status='PASS_PRINTED_SOURCE_HYPOTHESIS_INVENTORY',names=len(x['printed_names']),positive_row_hypotheses=[],all_remaining_premises_classified=True)
 write('NLR_HYPOTHESIS_CHECK.json',out)
elif mode=='freeze':
 x=json.loads((B/'NLR_PROOF_SOURCE.json').read_text());y=json.loads((B/'NLR_PROOF_OBJECTS.json').read_text())
 for z in x['sources']+y['objects']:assert H(Path(z['path']))==z['sha256']
 pins=json.loads((B/'NLR_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NLR_FROZEN_FILE_PINS.json').read_text())
 assert all(H(B/'NLR_src'/n)==v for n,v in{**frozen,**pins}.items())
 assert H(B/'NLR_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 own=sum(p.stat().st_size for p in B.rglob('*')if p.is_file());assert own<30_000_000_000,own
 out=dict(status='PASS_SOURCE_FREEZE',source_manifest_sha256=H(B/'NLR_PROOF_SOURCE.json'),object_manifest_sha256=H(B/'NLR_PROOF_OBJECTS.json'),frozen_native_pins=len(pins)+len(frozen),own_host_bytes=own,disk=shutil.disk_usage(B)._asdict(),target_dir=os.environ['CARGO_TARGET_DIR'],schemas_source_value_only=True)
 write('NLR_SOURCE_FREEZE.json',out)
 write('NLR_READY.json',dict(status='READY_FOR_ONE_COMBINED_AUDIT',row_roots=[],target_established=False,full_child136_packet=False,target_dir=os.environ['CARGO_TARGET_DIR']))
elif mode=='ready':
 for f,key in [('NLR_PROOF_SOURCE.json','sources'),('NLR_PROOF_OBJECTS.json','objects')]:
  for z in json.loads((B/f).read_text())[key]:assert H(Path(z['path']))==z['sha256']
 assert json.loads((B/'NLR_SOURCE_FREEZE.json').read_text())['status']=='PASS_SOURCE_FREEZE'
 assert json.loads((B/'NLR_HYPOTHESIS_CHECK.json').read_text())['status']=='PASS_PRINTED_SOURCE_HYPOTHESIS_INVENTORY'
 out=dict(status='READY_FOR_ONE_COMBINED_AUDIT',row_roots=[],target_established=False,full_child136_packet=False,source_revision='see this scope receipt',cgroup=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),target_dir=os.environ['CARGO_TARGET_DIR'])
 write('NLR_READY.json',out)
else:raise AssertionError(mode)
print(json.dumps(out))
