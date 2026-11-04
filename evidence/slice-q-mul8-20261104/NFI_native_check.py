"""Strict additive validation of local windows, never a physical row instance."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def validate():
 by={int(p.parent.name[-3:]):obj(p) for p in E.glob('NFI_K*/receipt.json')}
 assert set(by)==set(range(1,101))
 groups=[]
 for lo,hi,cp,cn in [(6,12,4,5),(16,34,14,15),(41,49,39,40),(53,57,51,52),(61,63,59,60),(67,75,65,66),(79,89,77,78),(93,99,91,92)]:
  for pos in range(lo,hi+1,2):
   p,n,c,d=[by[i] for i in [pos,pos+1,cp,cn]]
   assert p['module']==n['module']
   assert [x['exit_status'] for x in [p,n,c,d]]==[0,1,0,1]
   for r,verdict in [(p,'SUCCESSFUL'),(n,'FAILED'),(c,'SUCCESSFUL'),(d,'FAILED')]:
    log=(E/r['attempt']/'stdout.log').read_text();assert 'VERIFICATION:- '+verdict in log and 'timed out' not in log
   hashes=[sha(E/r['attempt']/'NFI_harness.patch') for r in [p,n,c,d]]
   assert len(set(hashes))==1,(pos,hashes)
   groups.append(dict(positive=p['attempt'],negative=n['attempt'],kmx_positive=c['attempt'],kmx_negative=d['attempt'],exact_same_payload=True,status='LOCAL_CONTROLLED_WINDOW',composed_row_credit=False))
 for i,r in by.items():
  a=r['attempt'];ad=obj(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert r['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  g=obj(E/(a+'-graph-check.json'));assert g['graph_matches_frozen'] and g['resolved_features_all_crates']
  lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert obj(E/(a+'-rule16-check.json'))['static_declarations']==[]
  for name,h in r['source_hashes'].items():assert sha(E/a/'sources'/name)==h,(a,name)
  assert not (E/a/'sources/NFI_FROZEN.json').exists(),'duplicated large corpus'
  ref=obj(E/a/'sources/NFI_FROZEN_REF.json');assert ref['sha256']==sha(E.parent/'slice-q-mul7-20261104/NFF_FROZEN.json')
 assert len(groups)==39
 return dict(status='PASS_LOCAL_PROVENANCE_NO_ROW_INSTANCE',attempts=100,groups=groups,excluded={'NFI_K003':'own codegen initializer omission; no semantic result','NFI_K038':'90-second timeout of original allocation one-cell check; split into K061–064; no unchanged rerun'},option_fn_credits=[],writable_static_credits=[],contracts=[],newly_closed=[],physical_obligation='Native StepBy running-state relation and preservation on every actual reached outer-loop prestate')
if __name__=='__main__':
 x=validate();(E/'NFI_NATIVE_VALIDATION.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(status=x['status'],attempts=x['attempts'],groups=len(x['groups']))))
