from NGL_prepare import update,E,P
import json
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'r1_pool_adapter_owned.rs']
old='''fn require_zero(mut remaining: &[u8]) -> ProgramResult {
    while !remaining.is_empty() {
        if remaining[0] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
        remaining = &remaining[1..];
    }
    Ok(())
}'''
new='''fn require_zero(mut remaining: &[u8]) -> ProgramResult {
    while !remaining.is_empty() {
        #[cfg(kani)] let NGL_before = (remaining.as_ptr(), remaining.len());
        if remaining[0] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
        remaining = &remaining[1..];
        #[cfg(kani)] { NGL_owned::zero_frame(remaining.as_ptr(),remaining.len(),NGL_before.0,NGL_before.1); break; }
    }
    Ok(())
}'''
assert s.count(old)==1;s=s.replace(old,new)
h=I[P+'NGL_owned.rs'];h+='''
pub(super) fn zero_frame(after:*const u8,after_len:usize,before:*const u8,before_len:usize){assert_eq!(after,unsafe{before.add(1)});assert_eq!(after_len,before_len-1);}
fn zero_frame_wrong(after:*const u8,after_len:usize,before:*const u8,before_len:usize){assert!(after!=unsafe{before.add(1)}||after_len!=before_len-1);}
'''
attrs='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
body='let bytes:[u8;1768]=kani::any();let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=1768&&len<=1768-start);let input=&bytes[start..start+len];let r=require_zero(input);let expected=if len==0||input[0]==0{Ok(())}else{Err(ProgramError::AccountAlreadyInitialized)};assert_eq!(r,expected);'
h+='\n'+attrs+'fn zero_iteration(){'+body+'}\n'
h+='\n'+attrs+'#[kani::stub(zero_frame,zero_frame_wrong)]\nfn zero_iteration_frame_wrong(){'+body+'}\n'
h+='\n'+attrs+'fn zero_iteration_result_wrong(){'+body.replace('assert_eq!(r,expected)','assert_ne!(r,expected)')+'}\n'
update({P+'r1_pool_adapter_owned.rs':s,P+'NGL_owned.rs':h},'zero_iteration')
(E/'NGL_ZERO_SOURCE_ERASURE.json').write_text(json.dumps(dict(frozen_body=old,instrumented_body=new,erasure='Remove the two cfg(kani) statements; original frozen body is byte-identical',native_domain='arbitrary bytes[1768], 0<=start<=1768 and 0<=len<=1768-start, arbitrary suffix/window; at most ONE original loop iteration',model_domain='emitted indexed loop related by remaining=original.drop(index)'),indent=1)+'\n')
