"""Strict additive continuation of NDT/NED/NEE/NEJ; no inherited gate replaced."""
from pathlib import Path
import sys,json,copy,argparse,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(R/'evidence/slice-s-compose3-20261101'))
import NEJ_validate as predecessor
read=predecessor.read

def native_pair(positive,negative):
 """Additional support checks; a valid pair alone NEVER closes a ledger row."""
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
   for n in ['NEL_native_contracts.patch','NEL_oracle.patch']:
    source=(E/(a+'-'+n)).read_bytes()
    assert receipt['source_hashes'][n]==hashlib.sha256(source).hexdigest()
    assert b'static mut' not in source and b'stub_verified' not in source
  assert read(E/(positive+'.json'))['module']==read(E/(negative+'.json'))['module']
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError):return False

BASE_CERTIFICATE=predecessor.certificate
GETTER='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common'

def borrowed_projection(c,expected,ledger):
 try:
  import NEL_getter_identity as identity
  d=c['borrowed_projection']
  assert d['method']=='C3-BIN ruling (y-prime), 2026-11-01'
  assert d['function']==GETTER and (expected==GETTER or expected.startswith(GETTER+'::'))
  assert d['all_typed_inputs'] and d['empty_modifies'] and d['no_stub_verified']
  assert d['trust_classification']=='P6/D188 option A reclassification'
  assert d['native_support']
  for ref in d['native_support']:predecessor.inherited.artifact(ref)
  required={str((E/n).relative_to(R)) for a in ['NEL_K006','NEL_K007'] for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEL_native_contracts.patch',a+'-NEL_oracle.patch']}
  assert {r['path'] for r in d['native_support']}==required
  assert native_pair('NEL_K006','NEL_K007')
  record=json.loads(predecessor.inherited.artifact(d['source_identity']))
  assert record['frozen_revision']==ledger['frozen_revision']
  import subprocess
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+identity.PATH],cwd=R,text=True)
  assert identity.check(source) and record['exact_projection']==identity.EXPECTED
  assert record['source_sha256']==hashlib.sha256(source.encode()).hexdigest()
  assert d['extracted_identity']=='NED_ReconstructCarriers.common_argument'
  assert any(t['name']==d['extracted_identity'] for t in c['theorems'])
  audit=json.loads(predecessor.inherited.artifact(d['axioms_audit']))
  assert audit['exit_status']==0 and any("'NED_ReconstructCarriers.common_argument'" in l for l in audit['print_axioms'])
  for a,place in [('NEL_K006','=>common'),('NEL_K007','{ other }')]:
   code=(E/(a+'-NEL_oracle.patch')).read_text()
   assert '#[kani::stub(borrowed_common,designated)]' in code
   assert 'static mut' not in code and 'stub_verified' not in code
   assert 'frame.alternate' in (E/(a+'-NEL_native_contracts.patch')).read_text()
  assert ledger['frozen_revision']==identity.REV
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False

COMMON='crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common'
CANONICAL='crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical'

def scalar_caller(c,expected,ledger):
 try:
  q=c['framed_scalar_caller']
  assert q['method']=='ruling y: total scalar caller with local ordered child log'
  assert q['function']==COMMON and q['selected_child']==CANONICAL
  obs=[o for r in ledger['rows'] if r['function']==COMMON for o in r['caller_domain_obligations']]
  allowed={COMMON,COMMON+' -> '+CANONICAL}|{COMMON+'::'+h['name'] for r in ledger['rows'] if r['function']==COMMON for h in r['named_hypotheses']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  assert q['all_typed_inputs'] and q['local_frame_constructed'] and q['full_Result']
  assert q['empty_external_modifies'] and q['exact_body_projection']
  assert q['trust_classification']=='P6/D188 option A reclassification'
  assert q['shape']=='Result<(),PoolV1PaymentStatementFormatError>; mutable local record'
  assert q['controls']=={'native':'NEL_K034','contract':'NEL_K035','unimplied':'NEL_K039','inverted':'NEL_K040','frame':'NEL_K041'}
  from NEL_artifacts import native_support
  expected_support=native_support(['NEL_K032','NEL_K033','NEL_K034','NEL_K035','NEL_K039','NEL_K040','NEL_K041'])
  assert q['native_support']==expected_support
  for ref in q['native_support']:predecessor.inherited.artifact(ref)
  assert native_pair('NEL_K032','NEL_K033') and native_pair('NEL_K034','NEL_K040') and native_pair('NEL_K035','NEL_K041')
  # The unimplied check genuinely uses the same assertion as its real-body
  # control and the SAME weak body; only the supported substitution differs.
  u=read(E/'NEL_K039/receipt.json');text=(E/'NEL_K039/stdout.log').read_text()
  assert u['exit_status']!=0 and 'VERIFICATION:- FAILED' in text and 'Failed Checks:' in text and 'timed out' not in text.lower()
  assert u['limits']==read(E/'NEL_K034/receipt.json')['limits'] and int(u['swaps'])==0
  assert read(E/'NEL_K039-admission.json')['exit']==0 and read(E/'NEL_K039-admission.json')['reservation']['allowed'] is True
  assert read(E/'NEL_K039-graph-check.json')['graph_matches_frozen'] and read(E/'NEL_K039-graph-check.json')['exact_LPm_graph']
  assert read(E/'NEL_K039-lock-check.json')['unchanged'] and read(E/'NEL_K039-rule16-check.json')['no_writable_static']
  assert read(E/'NEL_K039.json')['env']['CARGO_NET_OFFLINE']=='true'
  import re,subprocess
  def added(a):return '\n'.join(l[1:] for l in (E/(a+'-NEL_native_contracts.patch')).read_text().splitlines() if l.startswith('+') and not l.startswith('+++'))
  native=added('NEL_K034');havoc=added('NEL_K039')
  weak=lambda t:next(l for l in t.splitlines() if l.startswith('fn weak('))
  assert weak(native)==weak(havoc)
  assert '#[kani::stub_verified(weak)]' not in native and '#[kani::stub_verified(weak)]' in havoc
  assert 'assert!(f.y==old,"unimplied external frame")' in native and 'assert!(f.y==old,"unimplied external frame")' in havoc
  assert 'Check that' in (E/'NEL_K041/stdout.log').read_text() and 'assignable' in (E/'NEL_K041/stdout.log').read_text()
  frozen=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+COMMON.split('::')[0]],cwd=R,text=True)
  a=frozen.index('fn validate_common(');z=frozen.index('\n}',a)+2;body=frozen[a:z]
  projected=body.replace('fn validate_common(common: CommonPublicV1)','fn NEL_common_validator(common: CommonPublicV1, frame:&mut NEL_common_validator::Frame)').replace('digest_is_canonical(&common.anchor_root)','NEL_common_validator::canonical(&common.anchor_root,frame)').replace('digest_is_canonical(&common.nullifier)','NEL_common_validator::canonical(&common.nullifier,frame)')
  source=added('NEL_K032');assert projected in source
  assert '#[kani::modifies(&mut frame.log)]' in source
  assert '#[kani::requires(frame.log==0 && common.pool==frame.expected.pool' in source
  assert q['positive']=='NEL_K032' and q['negative']=='NEL_K033'
  assert [t['name'] for t in q['model_theorems']]==['NEL_CommonOracle.substitution','NEL_CommonOracle.reached_argument','NEL_CommonOracle.call_count']
  assert [t['name'] for t in q['emitted_association']]==['NED_CommonValidation.common_result','NED_PaymentCohorts.canonical_result']
  assert all(predecessor.inherited.theorem(t) for t in q['model_theorems']+q['emitted_association'])
  if c['kind']=='external-domain':
   row_ob=next(o for o in obs if o['id']==expected)
   assert row_ob['call'].get('expression',row_ob['call'].get('syntax')) in {'Err','Ok'}
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False

def certificate(c,expected,ledger,reviewed):
 if not c or not c.get('id','').startswith('NEL_'):return BASE_CERTIFICATE(c,expected,ledger,reviewed)
 if predecessor.predecessor.suspended_reference(c):return False
 # Original NDT/NED theorem, review, hypothesis and native-artifact gates.
 if not predecessor.predecessor.BASE_CERTIFICATE(c,expected,ledger,reviewed):return False
 # Original NEJ exact domain/physical/site gates are still mandatory.
 if not predecessor.call_domain(c,expected,ledger):return False
 return scalar_caller(c,expected,ledger) if 'framed_scalar_caller' in c else borrowed_projection(c,expected,ledger)

def compose(base,packet,reviewed):
 previous=predecessor.certificate
 try:
  predecessor.certificate=certificate
  return predecessor.compose(base,packet,reviewed)
 finally:predecessor.certificate=previous

def main():
 p=argparse.ArgumentParser();p.add_argument('--write',type=Path);a=p.parse_args()
 out=compose(read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),read(E/'NEL_LEDGER_DELTA.json'),read(E/'NEL_REVIEWED_CERTIFICATES.json'))
 if a.write:a.write.write_text(json.dumps(out,indent=1)+'\n')
 print(json.dumps(predecessor.summary(out),indent=1))
if __name__=='__main__':main()
