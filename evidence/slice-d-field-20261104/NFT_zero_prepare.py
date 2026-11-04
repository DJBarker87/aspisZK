from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent;R=E.parents[1];p=E/'NFT_NATIVE_INPUTS.json';x=json.loads(p.read_text());C='crates/aspis-core/src/'
# Standalone step retains the frozen ProgramError constructor using the core-independent
# verifier program harness; no Solana syscall, callback or account operation is reached.
n='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs';frozen=subprocess.check_output(['git','show','4bb3b3f:'+n],cwd=R,text=True)
code='''use super::*;
fn zero_cut(mut remaining:&[u8])->(u8,&[u8],ProgramResult){
 if !remaining.is_empty(){
  if remaining[0]!=0{return (1,remaining,Err(ProgramError::AccountAlreadyInitialized));}
  remaining=&remaining[1..];return (2,remaining,Ok(()));
 }
 (0,remaining,Ok(()))
}
#[kani::proof] #[kani::unwind(10)]
fn pointer4096(){let bytes:[u8;4096]=kani::any();let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=end&&end<=4096);let view=&bytes[start..end];let(tag,rest,_)=zero_cut(view);let shift=if tag==2{1}else{0};assert!((rest.as_ptr()==view.as_ptr().wrapping_add(shift))!=cfg!(NFT_invert));}
#[kani::proof] #[kani::unwind(10)]
fn result4096(){let bytes:[u8;4096]=kani::any();let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=end&&end<=4096);let view=&bytes[start..end];let(tag,_,r)=zero_cut(view);let want=if start==end{0}else if bytes[start]!=0{1}else{2};let good=tag==want&&if tag==1{matches!(r,Err(ProgramError::AccountAlreadyInitialized))}else{r.is_ok()};assert!(good!=cfg!(NFT_invert));}
#[kani::proof] #[kani::unwind(10)]
fn length4096(){let bytes:[u8;4096]=kani::any();let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=end&&end<=4096);let view=&bytes[start..end];let(tag,rest,_)=zero_cut(view);let shift=if tag==2{1}else{0};assert!((rest.len()==end-start-shift)!=cfg!(NFT_invert));}
#[kani::proof] #[kani::unwind(10)]
fn frame4096(){let bytes:[u8;4096]=kani::any();let start:usize=kani::any();let end:usize=kani::any();let probe:usize=kani::any();kani::assume(start<=end&&end<=4096&&probe<4096);let before=bytes[probe];let _=zero_cut(&bytes[start..end]);assert!((bytes[probe]==before)!=cfg!(NFT_invert));}
'''
def body(s,marker):
 a=s.index('{',s.index(marker));b=a+1;depth=1
 while depth:depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a+1:b-1]
original=body(frozen,'fn require_zero(');cut=body(code,'fn zero_cut(');erased=cut.replace('if !remaining.is_empty()','while !remaining.is_empty()',1).replace('return (1,remaining,Err(ProgramError::AccountAlreadyInitialized));','return Err(ProgramError::AccountAlreadyInitialized);').replace('return (2,remaining,Ok(()));','').replace('(0,remaining,Ok(()))','Ok(())');normalize=lambda s:re.sub(r'\s+','',s);assert normalize(original)==normalize(erased)
x[n]=frozen+'\n#[cfg(kani)]\n#[path="NFT_zero.rs"]\nmod NFT_zero;\n';x['programs/r1-cost-probe/src/NFT_zero.rs']=code;p.write_text(json.dumps(x,indent=1)+'\n');p=E/'NFT_SOURCE_PINS.json';pins=json.loads(p.read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});p.write_text(json.dumps(pins,indent=1)+'\n');(E/'NFT_zero.rs.txt').write_text(code)
(E/'NFT_ZERO_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),cut_sha256=hashlib.sha256(cut.encode()).hexdigest(),erasure_equal=True,scope='one arbitrary-prestate window within fully arbitrary 4096-byte backing; pointer, result, length and frame independently controlled',remaining='generic allocation/physical frame lift to the actual caller buffers, and composition with NFQ finite-loop model induction'),indent=1)+'\n')
