"""Validate receipt/control provenance; this never promotes a composed row."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
A=[obj(p) for p in E.glob('NFF_K*/receipt.json')];by={int(a['attempt'][-3:]):a for a in A}
assert len(A)==len(by)==90 and set(by)==set(range(1,91))
excluded={5:'incorrect own fold bound',25:'missing own canonical import',30:'timeout; redesigned/split, no credit',37:'stale own source pin, pre-Kani gate failure'}
groups=[(1,2,3,4),(11,12,13,14),(7,8,13,14),(15,16,17,18),(19,20,23,24),(21,22,23,24),(29,26,27,28),(31,32,35,36),(33,34,35,36),(45,38,39,40),(41,42,39,40),(43,44,39,40)]
groups += [(i,i+1,56,57) for i in range(46,56,2)]
groups += [(i,i+1,66,67) for i in range(58,66,2)]
groups += [(68,69,72,73),(70,71,72,73)]
groups += [(i,i+1,9,10) for i in range(74,90,2)]+[(90,6,9,10)]
records=[]
for pos,neg,cp,cn in groups:
 p,n,c,d=[by[i] for i in [pos,neg,cp,cn]]
 assert p['module']==n['module'] and p['exit_status']==c['exit_status']==0 and n['exit_status']==d['exit_status']==1
 assert all('VERIFICATION:- '+verdict in (E/r['attempt']/'stdout.log').read_text() for r,verdict in [(p,'SUCCESSFUL'),(n,'FAILED'),(c,'SUCCESSFUL'),(d,'FAILED')])
 hashes=[sha(E/r['attempt']/'NFF_harness.patch') for r in [p,n,c,d]]
 assert hashes[0]==hashes[1] and hashes[2]==hashes[3],(pos,neg,'unmatched native/control payload')
 exact=hashes[0]==hashes[2]
 for r in [p,n,c,d]:
  name=r['attempt'];g=obj(E/(name+'-graph-check.json'));lock=obj(E/(name+'-lock-check.json'));static=obj(E/(name+'-rule16-check.json'))
  assert g['graph_matches_frozen'] and not static['static_declarations'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert r['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert obj(E/(name+'-admission.json'))['exit']==0 and obj(E/(name+'-admission.json'))['reservation']['allowed'] is True
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  for name,h in r['source_hashes'].items():assert sha(E/r['attempt']/'sources'/name)==h,(r['attempt'],name)
 records.append(dict(positive=p['attempt'],negative=n['attempt'],kmx_positive=c['attempt'],kmx_negative=d['attempt'],native_same_payload=True,exact_kmx_same_payload=exact,status='LOCAL_CONTROLLED_WINDOW' if exact else 'COPY_CONFIGURATION_MISMATCH_NO_CREDIT',composed_row_credit=False))
result=dict(status='PASS_PROVENANCE_NO_ROW_PROMOTION',attempts=90,groups=records,excluded=excluded,option_fn_credits=[],writable_static_credits=[],contracts=[],newly_closed=[])
(E/'NFF_NATIVE_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],attempts=90,groups=len(records),exact_kmx=sum(r['exact_kmx_same_payload'] for r in records),copy_configuration_mismatches=[r['positive'] for r in records if not r['exact_kmx_same_payload']])))
