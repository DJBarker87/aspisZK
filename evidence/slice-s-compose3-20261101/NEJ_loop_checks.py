"""Additional rule-B gates for a same-execution Bool result plus state frame."""
from pathlib import Path
import json,hashlib,re,subprocess

def validate(c,expected,ledger,v):
 try:
  q=c['loop_composition'];assert q['method']=='rule B: one native step, Lean induction, emitted step association'
  assert q['shape']=='Bool' and q['invariant']=='0<=i<=8; canonical iff suffix from i; same external state'
  assert q['trust_classification']=='P6/D188 option A reclassification'
  assert q['inner_hypotheses_remaining']==[] and q['native_external_modifies']==[]
  assert q['case'] in ['forest','tree'];case=q['case'];f=q['function']
  module='pair_forest_accounts' if case=='forest' else 'pair_tree_profile'
  assert f=='crates/aspis-statement/src/pool_v1/'+module+'.rs::digest_is_canonical'
  arg='digest' if case=='forest' else 'value'
  obs=[o for row in ledger['rows'] if row['function']==f for o in row['caller_domain_obligations'] if 'callee' not in o]
  assert q['external_ids']==sorted({o['id'] for o in obs})
  assert all(o['call'].get('expression',o['call'].get('syntax'))==arg+'.len' for o in obs)
  assert expected==f or expected.startswith(f+'::') or expected in q['external_ids']
  assert q['external_length_theorem']['name']=='NEJ_ScannerWidth.width'
  assert v.inherited.theorem(q['external_length_theorem'])
  arg='digest' if case=='forest' else 'value'
  native_source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+f.split('::')[0]],cwd=v.R,text=True)
  header=('fn' if case=='forest' else 'pub(crate) fn')+' digest_is_canonical('+arg+': &Digest) -> bool {'
  a=native_source.index(header);z=native_source.index('\n}',a)+2;body=native_source[a:z]
  assert hashlib.sha256(body.encode()).hexdigest()==q['frozen_body_sha256']
  stepheader=header.replace('digest_is_canonical(','NEE_step(').replace(': &Digest)',': &Digest, frame: &mut NEE_loop_frame::Frame)')
  stepbody=body.replace(header,stepheader).replace('    let mut i = 0;','    let mut i = 0;\n    i = frame.start;').replace('        i += 1;','        i += 1;\n        frame.end = i; return true;')
  expr='{ let i=frame.start; let good=i>=8||'+arg+'[i].0<P;\n *r==good && frame.end==if i<8&&good {i+1} else {i} }'
  for kind in ['positive','negative']:
   p=q[kind];artifact=v.inherited.artifact
   rc=json.loads(artifact(p['receipt']));assert rc['kind']=='kani'
   assert (rc['exit_status']==0)==(kind=='positive') and rc['source_revision']
   assert rc['module']=='pool_v1::'+module+'::NEE_loop_frame::step_frame'
   assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
   assert int(rc['swaps'])==0 and int(rc['peak_rss_kib'])>0 and rc['wall_seconds']>=0
   text=artifact(p['contract']).decode();oracle=artifact(p['oracle']).decode()
   assert rc['source_hashes']['NEE_native_contracts.patch']==p['contract']['sha256']
   assert rc['source_hashes']['NEE_oracle.patch']==p['oracle']['sha256']
   assert not re.search(r'\bstatic\s+mut\b|\b(?:UnsafeCell|Atomic\w*)\b|Cell<|RefCell<',text+oracle)
   added='\n'.join(l[1:] for l in text.splitlines() if l.startswith('+') and not l.startswith('+++'))+'\n'
   assert stepbody in added
   assert '#[cfg_attr(kani,kani::requires(frame.start<=8 && frame.end==frame.start))]' in added
   assert '#[cfg_attr(kani,kani::modifies(&mut frame.end))]' in added
   assert '#[cfg_attr(kani,kani::ensures(|r| '+(expr if kind=='positive' else '!('+expr+')')+'))]' in added
   assert '#[kani::unwind(2)]' in added and '#[kani::proof_for_contract(NEE_step)]' in added
   assert 'pub(super) struct Frame {pub start:usize,pub end:usize}' in added
   log=artifact(p['stdout']).decode();assert 'timed out' not in log.lower()
   assert ('VERIFICATION:- SUCCESSFUL' if kind=='positive' else 'VERIFICATION:- FAILED') in log
   if kind=='negative':assert 'Failed Checks: |r|' in log
   graph=json.loads(artifact(p['graph']));assert graph['graph_matches_frozen'] and graph['exact_LPm_graph']
   lock=json.loads(artifact(p['lock']));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
   config=json.loads(artifact(p['config']));assert config['env']['CARGO_NET_OFFLINE']=='true' and config['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
   assert config['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
   assert json.loads(artifact(p['source_check']))['errors']==[]
   features=json.loads(artifact(p['features']));assert features['features_all_crates']
   actual=next(x['features'] for x in features['features_all_crates'] if x['name']=='aspis-statement')
   assert set(config['required_statement_features'])<=set(actual)
   ad=json.loads(artifact(p['admission']));assert ad['exit']==0 and ad['reservation']['allowed'] is True
  assert q['value_frame_theorem']['name']=='NEJ_ScannerFramed.value_and_frame'
  assert v.inherited.theorem(q['value_frame_theorem'])
  assert [t['name'] for t in q['emitted_association_theorems']]==['NED_ScannerCohorts.'+('account' if case=='forest' else 'profile')+'_body','NED_ScannerCohorts.'+('account' if case=='forest' else 'profile')+'_result']+(['NEE_CanonicalFrame.tree_body'] if case=='tree' else [])
  assert all(v.inherited.theorem(t) for t in q['emitted_association_theorems'])
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
