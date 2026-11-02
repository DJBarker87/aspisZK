"""Strict new native support; no historical suspension is restored."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest();obj=lambda p:json.loads(p.read_text())
CAPS=dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
def snapshot(a):
 raw=lzma.decompress((E/(a+'_INPUTS.json.xz')).read_bytes())
 assert sha(raw)==(E/(a+'_INPUTS.json.sha256')).read_text().split()[0]
 d=json.loads(raw);rc=obj(E/a/'receipt.json');assert set(d)==set(rc['source_hashes'])
 assert all(sha(text.encode())==rc['source_hashes'][name] for name,text in d.items())
 return d

def pair(pos,neg,target):
 records=[]
 for a,expected in [(pos,0),(neg,1)]:
  rc=obj(E/a/'receipt.json');src=snapshot(a)
  assert rc['kind']=='kani' and rc['exit_status']==expected and rc['limits']==CAPS and rc['swaps']=='0'
  assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert rc['copy_patch_sha256']==KMX and sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())==KMX
  assert rc['native_command'][rc['native_command'].index('--harness')+1]==target+('_wrong' if expected else '')
  assert obj(E/(a+'-graph-check.json'))['exact_frozen_selected_graph']
  lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']==LOCK
  assert not obj(E/(a+'-source-check.json'))['errors']
  admission=obj(E/(a+'-admission.json'));assert admission['exit_status']==0 and admission['reservation']['allowed'] is True
  log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log
  assert 'timed out' not in log.lower() and (not expected or '** 1 of ' in log)
  code=src['NEO_src/crates/aspis-core/src/field/NEO_parsers.rs']
  assert not re.search(r'\bstatic\s+mut\b|\bstatic\s+\w+\s*:[^;=]*(?:Atomic|UnsafeCell|RefCell|Cell\s*<)',code)
  assert not any(x in code for x in ['Option<fn','proof_for_contract','stub_verified'])
  assert '#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]' in code
  assert '#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]' in code
  records.append(rc)
 assert records[0]['source_hashes']==records[1]['source_hashes'] and records[0]['env']==records[1]['env']
 assert records[0]['native_command'][0:records[0]['native_command'].index('--harness')+1]==records[1]['native_command'][0:records[1]['native_command'].index('--harness')+1]
 return records

def review():
 # Exact KMX uses its own original correct/wrong names, not parser suffixes.
 for a,expected,tail in [('NEO_K002',0,'KMX_ptr_correct'),('NEO_K003',1,'KMX_ptr_wrong')]:
  d=obj(E/a/'receipt.json');snapshot(a);log=(E/a/'stdout.log').read_text()
  assert d['exit_status']==expected and d['limits']==CAPS and d['swaps']=='0' and d['copy_patch_sha256']==KMX
  assert d['native_command'][d['native_command'].index('--harness')+1]=='field::NEO_parsers::KMX_checks::'+tail
  assert ('VERIFICATION:- SUCCESSFUL' if not expected else 'VERIFICATION:- FAILED') in log and (not expected or '** 1 of ' in log)
  assert obj(E/(a+'-graph-check.json'))['exact_frozen_selected_graph'] and obj(E/(a+'-lock-check.json'))['unchanged']
 result={}
 for fn,pos,neg,target in [('M31::from_le_bytes','NEO_K015','NEO_K016','m_stdref'),('WideExact::from_limbs','NEO_K017','NEO_K018','limbs_ref')]:
  records=pair(pos,neg,'field::NEO_parsers::'+target);src=snapshot(pos)
  copy_rc=obj(E/'NEO_K002/receipt.json')
  for record in records:
   assert record['env']==copy_rc['env'],'copy control configuration drift'
   assert obj(E/(pos+'-graph-check.json'))['resolved_features_all_crates']==obj(E/'NEO_K002-graph-check.json')['resolved_features_all_crates'],'copy control features drift'
  assert sha(src['NEO_TOOL_PINS.json'].encode())==sha(snapshot('NEO_K002')['NEO_TOOL_PINS.json'].encode()),'copy tools drift'
  ex=obj(E/'NEO_REPRESENTATION_EXTRACTION_PINS.json');assert ex['exit']==0
  assert ex['rust_reference_sha256']==sha(src['NEO_src/crates/aspis-core/src/field/NEO_parser_reference.rs'].encode())==sha((E/'NEO_parser_reference.rs').read_bytes())
  for path,digest in ex['outputs'].items():
   assert sha((E/path).read_bytes())==digest,'raw extraction output drift'
   if path.endswith('.lean'):
    copied=E/'NEO_ParserRef'/Path(path).name
    assert sha(copied.read_bytes())==digest,'compiled extraction copy drift'
  assert ex['toolchain']=='nightly-2026-09-17'
  assert ex['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' and ex['aeneas_sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
  frozen='crates/aspis-core/src/field.rs' if fn.startswith('M31') else 'crates/aspis-core/src/field/wide_exact.rs'
  actual=src['NEO_src/'+frozen];old=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+frozen],cwd=R,text=True)
  assert actual==(old+'\n#[cfg(kani)]\nmod NEO_parsers;\n' if fn.startswith('M31') else old)
  result[fn]=dict(status='PASS',positive=pos,negative=neg,source_hashes=records[0]['source_hashes'],frozen_source_file=frozen,k3_status='UNAFFECTED',k2_quarantined=False,copy_controls=['NEO_K002','NEO_K003'],reference_extraction='NEO_E001',contract_uses=[],historical_suspensions_restored=[],qualification='Same selected fixed-width domain only; no arbitrary slice backing claimed')
 return result
if __name__=='__main__':
 result=review();(E/'NEO_NATIVE_REVIEW.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps({k:v['status'] for k,v in result.items()}))
