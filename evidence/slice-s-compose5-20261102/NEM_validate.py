"""Additive NEM continuation: every NEL and earlier check remains active."""
from pathlib import Path
import sys,json,argparse,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(R/'evidence/slice-s-compose4-20261101'))
import NEL_validate as predecessor
read=predecessor.read

def native_pair(positive,negative,folder=None,prefix="NEM_"):
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
    assert b'static mut' not in source and b'stub_verified' not in source
  assert read(E/(positive+'.json'))['module']==read(E/(negative+'.json'))['module']
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError):return False

BASE_CERTIFICATE=predecessor.certificate
inherited=predecessor.predecessor.inherited
DIGEST='crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical'

def digest(c,expected,ledger):
 try:
  q=c['digest_composition']
  assert q['function']==DIGEST and q['method']=='rule B: native Enumerate and same-call byte step; accepted suffix induction'
  assert q['all_raw_words'] and q['arbitrary_prestate'] and q['empty_external_modifies']
  assert q['trust_classification']=='P6/D188 option A reclassification' and q['no_new_trust_rows']
  assert q['native_pairs']==[['NEM_K002','NEM_K003'],['NEM_K004','NEM_K005']]
  assert all(native_pair(*pair) for pair in q['native_pairs'])
  from NEM_artifacts import native_support
  assert q['native_support']==native_support([a for pair in q['native_pairs'] for a in pair])
  for ref in q['native_support']:inherited.artifact(ref)
  # Exact source projection; no omitted statements or renamed native body.
  import subprocess
  f=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+DIGEST.split('::')[0]],cwd=R,text=True)
  a=f.index('pub fn encode_digest_canonical(');z=f.index('\n}',a)+2;body=f[a:z]
  assert body==q['frozen_body'] and hashlib.sha256(body.encode()).hexdigest()==q['frozen_body_sha256']
  assert body=='pub fn encode_digest_canonical(digest: &Digest) -> [u8; 32] {\n    let mut bytes = [0u8; 32];\n    for (index, value) in digest.iter().enumerate() {\n        bytes[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());\n    }\n    bytes\n}'
  wanted=['NEM_DigestInstance.next_call','NEM_DigestInstance.result_and_frame','NEL_DigestLoopFrame.step_and_bytes']
  assert [t['name'] for t in q['theorems']]==wanted
  assert all(inherited.theorem(t) for t in q['theorems'])
  for a in ['NEM_K004','NEM_K005']:
   code=(E/(a+'-NEM_native_contracts.patch')).read_text()
   assert 'let (index,value)=iter.next().unwrap();let reply=serialize(value,&d[' in code
   assert 'let dst=&mut bytes[index*4..index*4+4];let mut i=offset;dst[i]=reply[i];i+=1;' in code
   assert 'if j==cursor*4+offset{f.reply[offset]}else{old}' in code
  assert 'serialize(value,&d[cursor],&mut f)' in (E/'NEM_K004-NEM_native_contracts.patch').read_text()
  assert 'serialize(value,&d[(cursor+1)%8],&mut f)' in (E/'NEM_K005-NEM_native_contracts.patch').read_text()
  assert q['invariant']=='count=index; suffix=d[index..]; 0<=index<=8; arbitrary output; eight-index decreasing induction'
  rs=[r for r in ledger['rows'] if r['function']==DIGEST]
  obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={DIGEST}|{DIGEST+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{DIGEST+' -> crates/aspis-core/src/field.rs::M31::to_le_bytes'}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  if c['kind']=='external-domain':
   call=next(o for o in obs if o['id']==expected)['call']
   assert call.get('expression',call.get('syntax')) in {'digest.iter().enumerate','digest.iter','bytes[index * 4..index * 4 + 4].copy_from_slice'}
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False

def common(c,expected,ledger):
 import NEM_common_checks
 return NEM_common_checks.validate(c,expected,ledger,sys.modules[__name__])

def certificate(c,expected,ledger,reviewed):
 if not c or not c.get('id','').startswith('NEM_'):return BASE_CERTIFICATE(c,expected,ledger,reviewed)
 if predecessor.predecessor.predecessor.suspended_reference(c):return False
 if not predecessor.predecessor.predecessor.BASE_CERTIFICATE(c,expected,ledger,reviewed):return False
 if not predecessor.predecessor.call_domain(c,expected,ledger):return False
 if 'digest_composition' in c:return digest(c,expected,ledger)
 if 'encoder_composition' in c:
  import NEM_encoder_checks
  return NEM_encoder_checks.validate(c,expected,ledger,sys.modules[__name__])
 if 'frontier_validator' in c:
  import NEM_validator_checks
  return NEM_validator_checks.validate(c,expected,ledger,sys.modules[__name__])
 if 'lane_composition' in c:
  import NEM_lane_checks
  return NEM_lane_checks.validate(c,expected,ledger,sys.modules[__name__])
 if 'payment_encode_composition' in c:
  import NEM_payment_checks
  return NEM_payment_checks.validate(c,expected,ledger,sys.modules[__name__])
 return common(c,expected,ledger)

def compose(base,packet,reviewed):
 previous=predecessor.certificate
 try:
  predecessor.certificate=certificate
  return predecessor.compose(base,packet,reviewed)
 finally:predecessor.certificate=previous


def main():
 p=argparse.ArgumentParser();p.add_argument('--write',type=Path);a=p.parse_args()
 out=compose(read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),read(E/'NEM_LEDGER_DELTA.json'),read(E/'NEM_REVIEWED_CERTIFICATES.json'))
 if a.write:a.write.write_text(json.dumps(out,indent=1)+'\n')
 print(json.dumps(predecessor.predecessor.summary(out),indent=1))
if __name__=='__main__':main()
