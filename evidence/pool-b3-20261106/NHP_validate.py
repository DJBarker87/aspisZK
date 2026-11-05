"""Additive Pool-consumer validation; frozen 599 rows and historical rules preserved."""
from pathlib import Path
import sys,json,hashlib,lzma,re,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
STANDARD={'propext','Classical.choice','Quot.sound'}
def validate(overrides=None):
 overrides=overrides or {}
 def raw(n):return overrides.get(n,(E/n).read_bytes())
 def js(n):return json.loads(raw(n))
 import NHP_sparse_imports
 sys.path.insert(0,str(E.parent/'native-ledger3-20261029'))
 import NDT_validate
 NDT_validate.validate_invariants(json.loads((E.parent/'native-ledger3-20261029/NDT_LEDGER.json').read_text()))
 basis=E.parent/'inv-repair-20261104/NGB_ADMITTED_LEDGER.json.xz'
 assert H(basis.read_bytes())=='01de8c9429d5a2ab14b6d11aa5d8ce3c27e6a9ef72d2489f17eb7293224d4280'
 assert len(json.loads(lzma.decompress(basis.read_bytes()))['rows'])==599
 attempts=[json.loads(l) for l in raw('NHP_ATTEMPTS.jsonl').decode().splitlines()];ids=[a['attempt'] for a in attempts];assert len(ids)==len(set(ids))
 counts={k:sum(a.startswith('NHP_'+p) for a in ids) for k,p in [('kani','K'),('lean','L'),('extraction','E')]};assert all(counts[k]<=v for k,v in dict(kani=120,lean=80,extraction=2).items())
 for a in ids:
  rc=js(a+'/receipt.json');ad=js(a+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True,(a,'admission')
  assert rc['limits']==LIMITS and int(rc['swaps'])==0 and float(rc['wall_seconds'])>=0 and int(rc['peak_rss_kib'])>0
  assert rc['source_revision'] and rc['source_hashes'] and rc['command']
  for name,h in rc['source_hashes'].items():
   ref=js(a+'/sources/'+name+'.REFERENCE.json');payload=lzma.decompress(raw(ref['compressed']));assert H(payload)==h==ref['sha256'] and len(payload)==ref['bytes'],(a,name,'compiled input')
  if a.startswith(('NHP_K','NHP_E')):
   cfg=js(a+'.json');graph=js(a+'-graph-check.json');lock=js(a+'-lock-check.json');rule=js(a+'-rule16-check.json')
   assert graph['graph_matches_frozen'] and graph['exact_LPm_graph'] and not graph['added'] and not graph['edge_errors']
   assert lock==dict(before=LOCK,after=LOCK,unchanged=True)
   assert rule['no_writable_static'] and not rule['violations']
   assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and cfg['copy_patch_sha256']==KMX
   assert cfg['program_features']=='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit'
   assert js(a+'-metadata-pin.json')['features_all_crates']
  if a.startswith('NHP_L') and rc['exit_status']==0:
   assert all('sorryAx' not in line and ('depends on axioms' not in line or set(re.findall(r'\b(?:propext|Classical.choice|Quot.sound|sorryAx)\b',line))<=STANDARD) for line in rc['print_axioms'])
 closed=js('NHP_CLOSED.json');delta=js('NHP_LEDGER_DELTA.json');assert len(closed['composed_rows'])==delta['composed_rows_added']==len(delta['rows'])==2
 assert closed['production_association'] is False and closed['release_claim'] is False and closed['verifier_inventory_changed'] is False
 assert delta['basis']['rows']==599 and delta['root_status']=={'POOL.prefix_to_cpi':'OPEN','POOL.read_to_settlement':'OPEN'}
 for name in closed['certificates']:
  cert=js(name);assert cert['status']==cert['bridge_status']==cert['composed_status']=='CLOSED'
  assert cert['named_hypotheses']==cert['caller_domain_obligations']==cert['open_transitive_dependencies']==cert['modifies']==[]
  assert cert in delta['rows'] and cert['row'] in closed['composed_rows']
  assert cert['combined_replay']=='NHP_L009' and cert['raw_audit']=='NHP_L014' and cert['loaded_scan']=='NHP_L015'
  base=R/cert['native_evidence_dir'];pos=cert['native_positive'];neg=cert['matched_control']
  assert json.loads((base/pos/'receipt.json').read_text())['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in (base/pos/'stdout.log').read_text()
  assert json.loads((base/neg/'receipt.json').read_text())['exit_status']==1 and 'VERIFICATION:- FAILED' in (base/neg/'stdout.log').read_text()
  assert 'CBMC timed out.' not in (base/neg/'stdout.log').read_text() and 'Failed Checks:' in (base/neg/'stdout.log').read_text()
 guard=js('NHP_GUARD_CERTIFICATE.json');assert guard['native_positive']=='NHP_K028' and guard['matched_control']=='NHP_K029' and guard['theorem']=='NHP_StackLaw.exact_reply'
 assert H((R/guard['reference_source']).read_bytes())==guard['reference_sha256']
 assert H(guard['frozen_body'].encode())==guard['frozen_body_sha256']
 assert '#[kani::proof_for_contract(super::require_transaction_level_invocation_v1)]' in js('NHP_K028-shape.json')['source']
 assert js('NHP_K028-shape.json')['source'].replace('let admitted=crate::','let admitted=!crate::')==js('NHP_K029-shape.json')['source']
 error=js('NHP_POOL_ERROR_CERTIFICATE.json');assert error['native_positive']=='NHC_K078' and error['matched_control']=='NHC_K079' and error['theorem']=='NHC_ErrorConversion.result' and '(ak)' in error['route']
 for row in js('NHP_ERROR_REUSE.json')['inputs']:assert H((R/row['path']).read_bytes())==row['sha256']
 audit=js('NHP_AUDIT.json');assert audit['standard_only'] and audit['compiled_fixture_binary_identical'] and audit['roots']==19 and not audit['summary_disagreements']
 for a in ['NHP_L009','NHP_L013','NHP_L014','NHP_L015']:assert js(a+'/receipt.json')['exit_status']==0
 roots=js('NHP_audit/batch0/proof0.json')['results'];assert len(roots)==19 and all(x['equal'] and set(x['walked_axioms'])<=STANDARD for x in roots)
 fx=js('NHP_audit/fixtures/fixtures.json')['results'];assert len(fx)==8
 for i,x in enumerate(fx):assert x['equal'] and (len(x['walked_axioms'])==1 if i<4 else x['walked_axioms']==[])
 for row in map(json.loads,raw('NHP_LOADED_scan.jsonl').decode().splitlines()):assert not row['dangling'] and not row['duplicate_owners'] and row['imports_match']
 assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs','Cargo.lock'],cwd=R).returncode==0
 return dict(status='PASS',budget_used=counts,closed=2,verifier_rows=599,roots=19)
if __name__=='__main__':
 out=validate();(E/'NHP_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
