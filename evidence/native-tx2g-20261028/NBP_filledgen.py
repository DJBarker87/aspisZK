from pathlib import Path
import difflib,subprocess
E=Path(__file__).resolve().parent
s=''
for name,t,size in [('u8','u8',1),('u32','u32',4),('u64','u64',8),('block','[u8;32]',32)]:
 s+=f'''#[kani::proof]
#[kani::unwind(64)]
fn NBP_capacity_{name}() {{
 let n:usize=kani::any();kani::assume(n>(isize::MAX as usize)/{size});
 let value:{t}=kani::any();
 match super::filled(n,value) {{Err(super::Error::Allocation)=>(),_=>assert!(false)}}
 kani::cover!(n==usize::MAX);
}}
'''
s+='''#[kani::proof]
#[kani::unwind(64)]
fn NBP_filled_zero() {
 let value:u64=kani::any();
 match super::filled(0,value) {Ok(v)=>{assert!(v.len()==0);assert!(v.capacity()==0);},_=>assert!(false)}
 kani::cover!(value==u64::MAX);
}
'''
p='crates/aspis-core/src/r0/heap.rs';old=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);new=old+'\n#[cfg(kani)]\nmod NBP_filled;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-core/src/r0/heap/NBP_filled.rs'))
(E/'NBP_filled.rs').write_text(s);(E/'NBP_filled.patch').write_text(patch)
old=(E/'NBP_error.rs').read_text()+(E/'NBP_components.rs').read_text()
s='''static mut NBP_FORMAT_PTR:*const u8=core::ptr::null();
fn NBP_format_reply(_args:core::fmt::Arguments<'_>)->String {
 let s=String::from("x");unsafe{NBP_FORMAT_PTR=s.as_ptr();}s
}
fn NBP_log_reply(s:&str) {unsafe{
 assert!(s.as_ptr()==NBP_FORMAT_PTR);assert!(s.len()==1);assert!(s.as_bytes()[0]==b'x');NBP_CALLS+=1;
}}
#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(std::fmt::format,NBP_format_reply)]
#[kani::stub(solana_program::log::sol_log,NBP_log_reply)]
fn NBP_error_forward() {
 let tag:u8=kani::any();kani::assume(tag<8);
 use aspis_r1_cost_probe::verifier::Error;
 let e=match tag{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation};
 unsafe{NBP_CALLS=0;}
 assert!(super::error(e)==solana_program::program_error::ProgramError::InvalidInstructionData);
 unsafe{assert!(NBP_CALLS==1);}
 kani::cover!(tag==7);
}
'''
p='programs/r1-cost-probe/src/NBP_error.rs'
(E/'NBP_forward.rs').write_text(s)
(E/'NBP_forward.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),(old+s).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
