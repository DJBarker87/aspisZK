"""First root only: concrete caller and all reached child instances required."""
import json,hashlib,subprocess
F='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1'
CHILDREN=['crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1','crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1','crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1','crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1']

def validate(c,expected,ledger,v):
 try:
  q=c['validator_root'];assert q['function']==F
  assert q['method']=='ruling y: frozen native caller, CLOSED child substitutions on same calls, concrete G theorem'
  assert q['child_functions']==CHILDREN and q['inner_hypotheses_remaining']==[]
  assert q['domain']=='every typed terminal Statement; valid root physical carrier; no acceptance or inner domain premise'
  assert q['trust_classification']=='P6/D188 option A reclassification'
  assert q['native_pairs']==[['NEE_K052','NEE_K053'],['NEL_K006','NEL_K007']]
  P=v.R/'evidence/slice-s-compose2-20261029';L=v.R/'evidence/slice-s-compose4-20261101'
  assert inherited_root_pair(v)
  assert v.native_pair('NEL_K006','NEL_K007',folder=L,prefix='NEL_')
  from NEM_artifacts import ref
  required=[]
  for folder,prefix,pair in [(P,'NEE_',['NEE_K052','NEE_K053']),(L,'NEL_',['NEL_K006','NEL_K007'])]:
   required += [ref(folder/n) for a in pair for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-'+prefix+'native_contracts.patch',a+'-'+prefix+'oracle.patch']]
  assert q['native_support']==required
  for r in required:v.inherited.artifact(r)
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+F.split('::')[0]],cwd=v.R,text=True);a=source.index('pub fn '+F.split('::')[1]+'(');z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  added='\n'.join(l[1:] for l in (P/'NEE_K052-NEE_native_contracts.patch').read_text().splitlines() if l.startswith('+') and not l.startswith('+++'))
  a=added.index('pub fn '+F.split('::')[1]+'(');z=added.index('\n}',a)+2;native_body=added[a:z]
  erased=native_body.replace('    frame: &mut NEE_oracle::Frame,\n','')
  for old,new in [('NEE_oracle::pay_t(public,frame)','encode_pool_v1_private_transfer_public_v1(public)'),('NEE_oracle::pay_w(public,frame)','encode_pool_v1_withdrawal_public_v1(public)'),('NEE_oracle::lane(&nullifier,frame)','pool_v1_pair_forest_output_lane_v1(&nullifier)'),('NEE_oracle::late(&common.lane_transition, &mut late_bytes,frame)','encode_pool_v1_pair_late_public_statement_v1(&common.lane_transition, &mut late_bytes)')]:erased=erased.replace(old,new)
  import re
  assert re.sub(r'\s+','',erased)==re.sub(r'\s+','',body),'frozen caller erasure mismatch' 
  assert q['full_Result'] and q['ordered_effects'] and q['empty_external_modifies']
  assert q['late_buffer']=='same locally zero-initialized 1520-byte allocation; arbitrary complete child mutation never escapes'
  wanted=['NEM_ValidatorComposed.result_state_effects','NEM_PaymentReached.payment_reached','NEM_LaneReached.lane_reached','NEM_LateOracle.late_reached']
  assert [t['name'] for t in q['theorems']]==wanted and all(v.inherited.theorem(t) for t in q['theorems'])
  native=(P/'NEE_K052-NEE_oracle.patch').read_text()
  for text in ['core::ptr::eq(p,expected)','d[j].0==expected[j].0','core::ptr::eq(s,&f.root.common().lane_transition)','out.len()==1520','assert!(out[j]==0)','out.copy_from_slice(&kani::any::<[u8;1520]>());','f.trace.push(4);f.late']:
   assert text in native
  assert 'source.erasure' not in q['domain']
  rs=[r for r in ledger['rows'] if r['function']==F];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={F}|{F+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{F+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False

def inherited_root_pair(v):
 positive,negative="NEE_K052","NEE_K053";folder=v.R/"evidence/slice-s-compose2-20261029";prefix="NEE_";read=v.read
 """Additional support checks; a valid pair alone NEVER closes a ledger row."""
 E=folder
 try:
  for a,want in [(positive,True),(negative,False)]:
   receipt=read(E/a/'receipt.json');cfg=read(E/(a+'.json'));log=(E/a/'stdout.log').read_text()
   assert receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
   assert receipt['kind']=='kani' and (receipt['exit_status']==0)==want
   assert float(receipt['wall_seconds'])>0 and int(receipt['peak_rss_kib'])>0 and int(receipt['swaps'])==0
   assert ('VERIFICATION:- SUCCESSFUL' if want else 'VERIFICATION:- FAILED') in log
   assert 'timed out' not in log.lower()
   if not want:assert 'Failed Checks:' in log
   ad=read(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
   graph=read(E/(a+'-graph-check.json'));assert graph['graph_matches_frozen'] and graph['exact_LPm_graph']
   lock=read(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
   features=read(E/(a+'-metadata-pin.json'));assert features['features_all_crates']
   assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
   assert cfg['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
   assert not read(E/(a+'-source-check.json'))['errors']
   assert read(E/(a+'-rule16-check.json'))['no_writable_static']
   for n in [prefix+'native_contracts.patch',prefix+'oracle.patch']:
    source=(E/(a+'-'+n)).read_bytes()
    assert receipt['source_hashes'][n]==hashlib.sha256(source).hexdigest()
    assert b'static mut' not in source and b'stub_verified' not in source
  assert read(E/(positive+'.json'))['module']=='pool_v1::pair_forest_terminal::NEE_oracle::oracle_domain_positive'
  assert read(E/(negative+'.json'))['module']=='pool_v1::pair_forest_terminal::NEE_oracle::oracle_domain_negative'
  assert (E/(positive+'-NEE_native_contracts.patch')).read_bytes()==(E/(negative+'-NEE_native_contracts.patch')).read_bytes()
  assert (E/(positive+'-NEE_oracle.patch')).read_bytes()==(E/(negative+'-NEE_oracle.patch')).read_bytes()
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError):return False
