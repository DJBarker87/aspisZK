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

def certificate(c,expected,ledger,reviewed):
 if not c or not c.get('id','').startswith('NEL_'):return BASE_CERTIFICATE(c,expected,ledger,reviewed)
 if predecessor.predecessor.suspended_reference(c):return False
 # Original NDT/NED theorem, review, hypothesis and native-artifact gates.
 if not predecessor.predecessor.BASE_CERTIFICATE(c,expected,ledger,reviewed):return False
 # Original NEJ exact domain/physical/site gates are still mandatory.
 if not predecessor.call_domain(c,expected,ledger):return False
 return borrowed_projection(c,expected,ledger)

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
