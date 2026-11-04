from pathlib import Path
import json,hashlib,difflib,subprocess,re
E=Path(__file__).resolve().parent;R=E.parents[1];n='programs/r1-cost-probe/src/NFQ_program.rs';inputs=json.loads((E/'NFQ_NATIVE_INPUTS.json').read_text());old=inputs[n]
code='''
// ONE frozen loop iteration. Tag 2 is a continuation, not native success.
fn zero_cut(mut remaining:&[u8])->(u8,&[u8],ProgramResult){
 if !remaining.is_empty(){
  if remaining[0]!=0{return (1,remaining,Err(ProgramError::AccountAlreadyInitialized));}
  remaining=&remaining[1..];
  return (2,remaining,Ok(()));
 }
 (0,remaining,Ok(()))
}
#[kani::proof]
fn zero_result_window(){
 let bytes:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);
 let (tag,_,r)=zero_cut(&bytes[..n]);let want=if n==0{0}else if bytes[0]!=0{1}else{2};
 let full=tag==want && if tag==1{matches!(r,Err(ProgramError::AccountAlreadyInitialized))}else{r.is_ok()};
 assert!(full != cfg!(NFQ_invert));
 kani::cover!(tag==0);kani::cover!(tag==1);kani::cover!(tag==2);
}
#[kani::proof]
fn zero_length_window(){
 let bytes:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);
 let (tag,rest,_)=zero_cut(&bytes[..n]);let shift=if tag==2{1}else{0};
 assert!((rest.len()==n-shift) != cfg!(NFQ_invert));
}
#[kani::proof]
fn zero_pointer_window(){
 let bytes:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);let view=&bytes[..n];
 let (tag,rest,_)=zero_cut(view);let shift=if tag==2{1}else{0};
 assert!((rest.as_ptr()==view.as_ptr().wrapping_add(shift)) != cfg!(NFQ_invert));
}
#[kani::proof]
fn zero_frame_window(){
 let bytes:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);
 let a=bytes[0];let b=bytes[1];let c=bytes[2];let d=bytes[3];
 let _=zero_cut(&bytes[..n]);
 assert!((bytes[0]==a&&bytes[1]==b&&bytes[2]==c&&bytes[3]==d) != cfg!(NFQ_invert));
}
'''
# Exact, token-level erasure of the source cut to the frozen loop.
source=subprocess.check_output(['git','show','4bb3b3f:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'],cwd=R,text=True)
start=source.index('fn require_zero(mut remaining: &[u8]) -> ProgramResult {');beg=source.index('{',start);depth=1;end=beg+1
while depth:
 if source[end]=='{':depth+=1
 if source[end]=='}':depth-=1
 end+=1
body=source[beg+1:end-1]
a=code.index('{',code.index('fn zero_cut'));depth=1;b=a+1
while depth:
 if code[b]=='{':depth+=1
 if code[b]=='}':depth-=1
 b+=1
cut=code[a+1:b-1]
erased=cut.replace('if !remaining.is_empty()','while !remaining.is_empty()',1).replace('return (1,remaining,Err(ProgramError::AccountAlreadyInitialized));','return Err(ProgramError::AccountAlreadyInitialized);').replace('return (2,remaining,Ok(()));','').replace('(0,remaining,Ok(()))','Ok(())')
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize(erased)==normalize(body),(erased,body)
(E/'NFQ_ZERO_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',function='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero',source_body_sha256=hashlib.sha256(body.encode()).hexdigest(),cut_sha256=hashlib.sha256(cut.encode()).hexdigest(),erasure_equal=True,native_domain='ONE arbitrary-prestate readable window, length 0..4; no whole-loop credit',remaining='General physical/frame lift from this window to arbitrary remaining length <=4096; native/model step association and induction. No CLOSED claim for require_zero.'),indent=2)+'\n')
new=old+code;inputs[n]=new;(E/'NFQ_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NFQ_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NFQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NFQ_zero.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
