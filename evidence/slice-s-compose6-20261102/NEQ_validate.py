"""Additive continuation: predecessor checks remain mandatory and unchanged."""
from pathlib import Path
import sys,json,argparse,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-s-compose5-20261102'))
import NEM_validate as predecessor
from NEQ_inputs import read
BASE_CERTIFICATE=predecessor.certificate
inherited=predecessor.inherited
import NEE_validate, NEJ_validate


def certificate(c,expected,ledger,reviewed):
 if not c or not c.get('id','').startswith('NEQ_'):return BASE_CERTIFICATE(c,expected,ledger,reviewed)
 if NEE_validate.suspended_reference(c):return False
 if not NEE_validate.BASE_CERTIFICATE(c,expected,ledger,reviewed):return False
 if not NEJ_validate.call_domain(c,expected,ledger):return False
 if 'payment_decode' in c:
  from NEQ_payment_decode_checks import validate
 elif 'unwrap_conversion' in c:
  from NEQ_unwrap_checks import validate
 elif 'common_decode' in c:
  from NEQ_common_decode_checks import validate
 elif 'decode_scalar' in c:
  from NEQ_decode_checks import validate
 elif 'nullifier_getter' in c:
  from NEQ_nullifier_checks import validate
 elif 'result_validator' in c:
  from NEQ_result_validator_checks import validate
 else:
  from NEQ_encoder_checks import validate
 return validate(c,expected,ledger,sys.modules[__name__])

def compose(base,packet,reviewed):
 previous=predecessor.certificate
 try:
  predecessor.certificate=certificate
  return predecessor.compose(base,packet,reviewed)
 finally:predecessor.certificate=previous

def native_pair(positive,negative,folder=None,prefix="NEQ_"):
 """Additional support checks; a valid pair alone NEVER closes a ledger row."""
 E=folder or globals()["E"]
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
    assert b'static mut' not in source
    import re
    assert all(x==b'weak' for x in re.findall(rb'kani::stub_verified\(([^)]+)\)',source))
  assert read(E/(positive+'.json'))['module']==read(E/(negative+'.json'))['module']
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError):return False

def main():
 p=argparse.ArgumentParser();p.add_argument('--write',type=Path);a=p.parse_args()
 out=compose(read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),read(E/'NEQ_LEDGER_DELTA.json'),read(E/'NEQ_REVIEWED_CERTIFICATES.json'))
 if a.write:a.write.write_text(json.dumps(out,indent=1)+'\n')
 print(json.dumps(predecessor.predecessor.predecessor.summary(out),indent=1))
if __name__=='__main__':main()
