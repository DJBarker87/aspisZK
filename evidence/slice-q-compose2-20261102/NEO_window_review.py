"""Native windows only: this audit does not award installed-caller credit."""
from NEO_native_review import *
def audit():
 out={}
 for name,pos,neg in [('complex','NEO_K053','NEO_K054'),('quadratic','NEO_K055','NEO_K056'),('wide','NEO_K057','NEO_K058')]:
  records=[]
  for a,expected in [(pos,0),(neg,1),('NEO_K061',0),('NEO_K062',1)]:
   rc=obj(E/a/'receipt.json');src=snapshot(a);records.append(rc)
   assert rc['exit_status']==expected and rc['limits']==CAPS and rc['swaps']=='0'
   assert rc['copy_patch_sha256']==KMX and rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
   ad=obj(E/(a+'-admission.json'));assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
   graph=obj(E/(a+'-graph-check.json'));assert graph['exact_frozen_selected_graph']
   assert graph['resolved_features_all_crates']==obj(E/(pos+'-graph-check.json'))['resolved_features_all_crates']
   lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']==LOCK
   assert not obj(E/(a+'-source-check.json'))['errors']
   log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log and 'timed out' not in log.lower()
   code=src['NEO_src/crates/aspis-core/src/field/NEO_parsers.rs']
   assert not any(x in code for x in ['static mut','Option<fn','stub_verified','proof_for_contract'])
   assert '#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]' in code and '#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]' in code
   path='crates/aspis-core/src/field.rs';old=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],cwd=R,text=True)
   assert src['NEO_src/'+path]==old+'\n#[cfg(kani)]\nmod NEO_parsers;\n'
  assert records[0]['source_hashes']==records[1]['source_hashes']
  for rc in records:
   env=dict(rc['env']);env['RUSTFLAGS']=env['RUSTFLAGS'].replace(' --cfg NEO_wrong_window','');assert env==records[0]['env']
  pins=obj(E/'NEO_WINDOW2_EXTRACTION_PINS.json');assert pins['exit']==0
  assert pins['rust_reference_sha256']==sha((E/'NEO_window_reference.rs').read_bytes())==records[0]['source_hashes']['NEO_src/crates/aspis-core/src/field/NEO_window_reference.rs']
  for f,h in pins['outputs'].items():assert sha((E/f).read_bytes())==h==sha((E/'NEO_WindowV2'/Path(f).name).read_bytes())
  out[name]=dict(positive=pos,negative=neg,copy_controls=['NEO_K061','NEO_K062'],extraction='NEO_E009',status='native-window-only',remaining=['Complete installed cohort carrier association','Caller same-buffer relocation/frame and exact slice width at every real use'],historical_credit_restored=[])
 return out
if __name__=='__main__':(E/'NEO_WINDOW_REVIEW.json').write_text(json.dumps(audit(),indent=1)+'\n')
