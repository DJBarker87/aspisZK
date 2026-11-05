from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';C='crates/aspis-r1-cost-probe/src/'
src=subprocess.check_output(['git','show',F+':'+C+'candidate.rs'],text=True);a=src.index("fn wide_view<'a>");start=src.index('{',a);i=start+1;depth=1
while depth:depth+=(src[i]=='{')-(src[i]=='}');i+=1
body=src[start:i];cut=body.replace('E::from_le_bytes','log.decode')
cut=cut.replace('round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT]', 'round0: &proof[compact::OFF_ROUND0+usize::from(cfg!(NHF_bad_view))..compact::OFF_FOLDED_ROOT]')
p=E/'NHF_wide.rs.txt';old=p.read_text();copy=old[old.index('#[kani::proof] #[kani::unwind(34)]',old.index('fn wide_copy')-300):] if False else old[old.rfind('#[kani::proof]'):]
# Keep the original copy harness body and its exact attributes.
copy=old[old.index('#[kani::proof]',old.index('fn wide_view_result')):]
head='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct DecodeLog {proof:usize,reply:Option<E>,calls:usize}
impl DecodeLog {fn decode(&mut self,bytes:&[u8])->Option<E>{self.calls+=1;assert!(bytes.as_ptr() as usize==self.proof+7495&&bytes.len()==32);self.reply}}
fn cut<'a>(proof:&'a[u8],semantic:&'a[u8],y1:&'a[u8],log:&mut DecodeLog)->Result<View<'a>,Error>
'''+cut+'''
// The overapproximation accepts every CLOSED decoder reply. Lean supplies its
// full byte/Option law on the SAME logged input; no decoder success is assumed.
fn wide_result(){
 let proof:[u8;57607]=kani::any();let semantic:[u8;13831]=kani::any();let y1:[u8;928]=kani::any();
 let words:[u32;8]=kani::any();let mut i=0;while i<8{kani::assume(words[i]<2147483647);i+=1;}
 let reply=if kani::any(){E::from_limbs(words)}else{None};
 let slot:usize=kani::any();kani::assume(slot<8);
 let mut log=DecodeLog{proof:proof.as_ptr() as usize,reply,calls:0};
 let result=cut(&proof,&semantic,&y1,&mut log);
 assert_eq!(log.calls,1);
 match (reply,result){
 (None,Err(e))=>assert!(e==Error::Parse),
 (Some(expected),Ok(v))=>{
  assert_eq!(v.inactive.to_limbs()[slot],expected.to_limbs()[slot]);
  assert!(v.variant==Variant::S2);
  assert!(v.semantic.as_ptr()==semantic.as_ptr()&&v.semantic.len()==13831);
  assert!(v.y1.as_ptr()==y1.as_ptr()&&v.y1.len()==928);
  assert!(v.round0.as_ptr()==proof[7527..].as_ptr()&&v.round0.len()==224);
  assert!(v.folded_root.unwrap().as_ptr()==proof[7751..].as_ptr());
  assert!(v.round1.as_ptr()==proof[7783..].as_ptr()&&v.round1.len()==224);
  assert!(v.final_message.as_ptr()==proof[8007..].as_ptr()&&v.final_message.len()==2048);
  assert!(v.query_bytes.is_empty());
 },_=>assert!(false),}
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn wide_view_result(){wide_result()}
'''
p.write_text(head+copy)
pins=json.loads((E/'NHF_SOURCE_PINS.json').read_text());pins[C+'NHF_wide.rs']=hashlib.sha256(p.read_bytes()).hexdigest();(E/'NHF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NHF_WIDE_CUT_SOURCE.json').write_text(json.dumps(dict(frozen_revision=F,original=body,local_record=cut,replacement='only E::from_le_bytes becomes local log.decode; cfg NHF_bad_view changes round0 start by one in matched control',remaining='pair exact input reply to CLOSED byte decoder; proof/semantic/y1 input arrays arbitrary full values'),indent=1)+'\n')
# Rebuild complete scratch patch from current committed input files.
lib=subprocess.check_output(['git','show',F+':'+C+'lib.rs'],text=True)
changes={C+'lib.rs':'#![cfg_attr(kani, feature(allocator_api))]\n'+lib,C+'candidate.rs':src+'\n#[cfg(kani)]\n#[path="NHF_wide.rs"]\nmod NHF_wide;\n',C+'NHF_wide.rs':p.read_text()}
patch=''.join(''.join(difflib.unified_diff((lib if n.endswith('/lib.rs') else src if n.endswith('/candidate.rs') else '').splitlines(True),t.splitlines(True),fromfile='a/'+n if not n.endswith('/NHF_wide.rs') else '/dev/null',tofile='b/'+n)) for n,t in changes.items());(E/'NHF_native.patch').write_text(patch)
p=E/'NHF_run.py';s=p.read_text();s=s.replace(" if os.environ.get('NHF_BAD_ALLOC'):"," if os.environ.get('NHF_BAD_VIEW'):config['env']['RUSTFLAGS']+=' --cfg NHF_bad_view'\n if os.environ.get('NHF_BAD_ALLOC'):");p.write_text(s)
