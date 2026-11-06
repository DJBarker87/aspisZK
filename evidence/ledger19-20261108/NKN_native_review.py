"""Read-only revalidation of candidate native receipts; no native jobs launched."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
H=lambda b:hashlib.sha256(b).hexdigest()
inherited=json.loads((E.parent/'field4-20261108/NKJ_INHERITED_NATIVE_PINS.json').read_text())
lookup={Path(n).name:n for group in inherited.values() for n in group}
def raw(p):
 if p.exists():return p.read_bytes()
 if Path(str(p)+'.xz').exists():return lzma.decompress(Path(str(p)+'.xz').read_bytes())
 if p.name=='receipt.json' or p.name=='stdout.log':
  anchor=lookup.get(p.parent.name+'-graph-check.json');path=str(Path(anchor).parent/p.parent.name/p.name) if anchor else None
 else:
  path=lookup.get(p.name)
  if path is None:
   anchor=lookup.get(p.name.split('-')[0]+'-graph-check.json');path=str(Path(anchor).parent/p.name) if anchor else None
 assert path,str(p)
 return subprocess.check_output(['git','show','HEAD:'+path])
receipts=[];pairs=[];families=[];pins=[]
for folder,pre in [('claims2','NKA'),('poseidon-state','NKG'),('field4','NKJ')]:
 p=E.parent/(folder+'-20261108');cs=json.loads((p/f'{pre}_CLOSED.json').read_text())
 actual_pairs={tuple(pair)for f in cs['functions']for pair in f['native_pairs']}
 if pre=='NKJ':
  actual_pairs|={(f'NKJ_K{a:03}',f'NKJ_K{b:03}')for a,b in [(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(27,28),(29,30),(31,32),(33,34),(35,36),(56,57),(63,64)]}
  for group in [(17,18,19,20,21),(22,23,24,25,26),(37,38,39,40,41),(58,59,60,61,62),(65,66,67,68,69)]:
   families.append(dict(provider=pre,attempts=[f'NKJ_K{n:03}'for n in group],shape='weak/inverse/real-body/unimplied-under-stub_verified/modifies'))
   actual_pairs.add((f'NKJ_K{group[0]:03}',f'NKJ_K{group[1]:03}'))
 allnames={n for pair in actual_pairs for n in pair}|{n for f in families if f['provider']==pre for n in f['attempts']}
 for n in sorted(allnames):
  rc=json.loads(raw(p/n/'receipt.json'));log=raw(p/n/'stdout.log').decode();gp=p/(n+'-graph-check.json') if pre!='NKG' else p/(n+'_validation/NHR_GRAPH_CHECK.json');lp=p/(n+'-lock-check.json') if pre!='NKG' else p/(n+'_validation/NKG_LOCK.json');g=json.loads(raw(gp));lock=json.loads(raw(lp))
  if pre=='NKG':
   assert not g['added'] and not g['edge_errors']
   g=dict(g,graph_matches_frozen=g['graph_matches_frozen'],lock_sha256=lock['before'])
   assert json.loads(raw(p/(n+'_validation/NKG_INPUTS.json')))['KMX_patch_sha256']==KMX
  assert rc['limits']==LIMITS and rc['env']['CARGO_NET_OFFLINE']=='true',n
  assert g['graph_matches_frozen'] and g['lock_sha256']==LOCK,n
  assert lock['unchanged']and lock['before']==lock['after']==LOCK,n
  a=json.loads(raw(p/(n+'-admission.json')));assert a['exit']==0 and a['reservation']['allowed']is True,n
  assert rc['exit_status']in [0,1] and 'VERIFICATION:- '+('SUCCESSFUL'if rc['exit_status']==0 else'FAILED')in log,n
  if rc['exit_status']:assert 'Failed Checks:'in log or 'is assignable'in log,n
  receipts.append(dict(provider=pre,attempt=n,exit=rc['exit_status'],receipt_sha256=H(raw(p/n/'receipt.json')),graph_sha256=H(raw(gp)),lock_sha256=H(raw(lp)),source_hashes=rc.get('source_hashes'),native_command=rc.get('native_command'),features=g.get('selected_closure')))
 for pair in sorted(actual_pairs):
  assert json.loads(raw(p/pair[0]/'receipt.json'))['exit_status']==0
  assert all(json.loads(raw(p/n/'receipt.json'))['exit_status']==1 for n in pair[1:])
  pairs.append(dict(provider=pre,positive=pair[0],matched_controls=list(pair[1:])))
 if pre=='NKJ':
  for family in families:
   expected=[0,1,0,1,1]
   for n,ex in zip(family['attempts'],expected):assert json.loads(raw(p/n/'receipt.json'))['exit_status']==ex
  assert '--solver kissat'in ' '.join(json.loads(raw(p/'NKJ_K005/receipt.json')).get('native_command',[]))
  for n in ['NKJ_K003','NKJ_K004']:
   rc=json.loads(raw(p/n/'receipt.json'));assert rc['exit_status']!=0 and rc['limits']==LIMITS
 for q in p.glob(pre+'*KMX*.patch'):
  assert H(q.read_bytes())==KMX;pins.append(dict(path=str(q),sha256=KMX))
(E/'NKN_NATIVE_REVIEW.json').write_text(json.dumps(dict(status='PASS_READ_ONLY_RECEIPT_REVALIDATION',receipts=receipts,pairs=pairs,returned_record_fidelity=families,copy_patch=pins,kani_launched=0,extraction_launched=0,field_multiplication_in_kani=False,backend_change='K003/K004 -> Kissat K005/K006; (ba)(2)(b), same caps',trust='ReviewedTranscription option-A reclassification; native transport retained'),indent=1)+'\n')
print(json.dumps(dict(status='PASS',receipts=len(receipts),pairs=len(pairs),record_families=len(families))))
