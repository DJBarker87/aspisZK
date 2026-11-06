"""Read-only revalidation of NLH native receipts; no Kani is launched."""
from pathlib import Path
import json,hashlib,lzma,re
E=Path(__file__).resolve().parent;P=E.parent/'terminal6-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
J=lambda p:json.loads(raw(p))
verified={};checks={};pairs=[]
graph=raw(P/'NLH_RESOLVED_GRAPH.json.xz');graph=lzma.decompress(graph);assert H(graph)==(P/'NLH_RESOLVED_GRAPH.json.sha256').read_text().strip()
for i in range(2,48):
 a=f'NLH_K{i:03}';r=J(P/a/'receipt.json');g=J(P/(a+'-graph-check.json'));lock=J(P/(a+'-lock-check.json'));ad=J(P/(a+'-admission.json'));ref=J(P/(a+'-graph.ref.json'))
 positive=i%2==0
 assert r['exit_status']==(0 if positive else 1)
 assert g['graph_matches_frozen']and not g['edge_errors']and not g['new_package_tuples']
 assert g['graph_sha256']==ref['raw_sha256']==H(graph)and ref['raw_bytes']==len(graph)
 assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert not J(P/(a+'-source-check.json'))['errors']
 assert r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and r['swaps']=='0'
 features={x['name']:set(x['features'])for x in g['selected_closure']}
 assert 'aspis-pool'not in features,'Pool outside selected closure'
 if 'aspis-r1-cost-probe'in features:assert {'default','optimized-terminal','private-leaf-salts','program-build'}<=features['aspis-r1-cost-probe']
 assert {'r0','pool-v1-kernel'}<=features['aspis-statement']and sum(x.endswith('-audit')for x in features['aspis-statement'])==12
 assert r['source_hashes']['NLH_KMX.patch']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 log=raw(P/a/'stdout.log').decode();assert 'VERIFICATION:- '+('SUCCESSFUL'if positive else'FAILED')in log
 if not positive:
  tail=log.split('VERIFICATION RESULT:',1)[1]
  assert 'unwinding assertion'not in tail and re.search(r'\*\* [1-9][0-9]* of [0-9]+ failed',tail),a
  assert 'core::panicking::assert_failed_inner'in tail,a
  count=int(re.search(r'\*\* ([0-9]+) of [0-9]+ failed',tail)[1]);assert count==(2 if i==25 else 1),a
  if i==25:assert 'assertion failed: !cfg!(NKR_invert)'in tail
 for n,h in r['source_hashes'].items():
  if h in verified:continue
  found=None
  for q in [P/a/'sources'/n,P/n]:
   try:b=raw(q)
   except FileNotFoundError:continue
   if H(b)==h:found=q;break
  assert found is not None,(a,n,'missing source')
  verified[h]=dict(path=str(found),bytes=len(b),sha256=h)
 checks[a]=dict(receipt_sha256=H(raw(P/a/'receipt.json')),graph_sha256=H(raw(P/(a+'-graph-check.json'))),lock_sha256=H(raw(P/(a+'-lock-check.json'))),positive=positive,exit=r['exit_status'],features={k:sorted(v)for k,v in features.items()},source_hashes=r['source_hashes'])
 if not positive:
  pos=f'NLH_K{i-1:03}';assert checks[pos]['source_hashes']==r['source_hashes'],(pos,a,'different input configurations')
  pairs.append(dict(positive=pos,negative=a,same_inputs=True))
(E/'NLS_NATIVE_REVIEW.json').write_text(json.dumps(dict(status='PASS',native_runs=0,retained_pairs=pairs,receipts=checks,retained_inputs=list(verified.values()),copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',Option_fn_credit=[],writable_static_credit=[],off_path_pool='Older predecessor Pool excluded from every selected native closure; no Pool credit',trust='P6/D188 option-A reclassification, never removal'),indent=1)+'\n')
print(json.dumps(dict(status='PASS',pairs=len(pairs),receipts=len(checks),inputs=len(verified))))
