from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-core/src/'
code=r'''include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn exercise(g:usize){
 let value:[u32;4]=kani::any();
 let p:usize=kani::any();kani::assume(p<64);let k:usize=kani::any();kani::assume(k<64);
 let mut out=Vec::with_capacity(64);out.resize(p,value);let allocated=out.as_ptr();
 out.resize(p+1,value);let delivered=out;
 let good=match g{
 0=>delivered.as_ptr()==allocated,
 1=>delivered.len()==p+1&&delivered[p][0]==value[0],
 2=>if k<p{delivered[k][0]==value[0]}else{true},
 4|5|6=>delivered[p][g-3]==value[g-3],
 _=>if k<p{delivered[k][g-6]==value[g-6]}else{true}};
 assert!(if cfg!(NHM_invert){!good}else{good});
}
struct ReserveLog{fail:bool,n:usize,calls:usize,ptr:*const [u32;4]}
fn reserve(out:&mut Vec<[u32;4]>,n:usize,l:&mut ReserveLog)->Result<(),()>{l.n=n;l.calls+=1;if l.fail{Err(())}else{out.reserve_exact(n);l.ptr=out.as_ptr();Ok(())}}
fn allocation_prefix(n:usize,l:&mut ReserveLog)->Result<Vec<[u32;4]>,crate::r0::Error>{
 let mut out=Vec::new();reserve(&mut out,n,l).map_err(|_|crate::r0::Error::Allocation)?;Ok(out)
}
#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn init03(){let fail:bool=kani::any();let mut l=ReserveLog{fail,n:0,calls:0,ptr:core::ptr::null()};let r=allocation_prefix(64,&mut l);let good=l.n==64&&l.calls==1&&match r{Err(e)=>fail&&matches!(e,crate::r0::Error::Allocation),Ok(v)=>!fail&&v.is_empty()&&v.as_ptr()==l.ptr&&v.capacity()>=64};assert!(if cfg!(NHM_invert){!good}else{good});}
macro_rules! gate{($name:ident,$n:expr)=>{#[kani::proof]#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[[u32;4]]>::to_vec,KMX_to_vec)]
fn $name(){exercise($n)}};}
'''+''.join(f'gate!(init{i:02},{i});\n'for i in [0,1,2,4,5,6,7,8,9])
inputs={C+'lib.rs':subprocess.check_output(['git','show','4bb3b3f:'+C+'lib.rs'],text=True).replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')+'\n#[cfg(kani)] #[path="NHM_init.rs"] mod NHM_init;\n',C+'NHM_init.rs':code}
patch=''
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True)
 patch+=''.join(difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n))
(E/'NHM_init.patch').write_text(patch)
