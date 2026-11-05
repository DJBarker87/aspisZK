from pathlib import Path
import subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn exercise(g:usize){
 let value:[u32;4]=kani::any();
 let n=if g<4 {1} else if g==4 {0} else {usize::MAX};
 let out=crate::r0::heap::filled(n,value);
 let good=if n==usize::MAX {matches!(out,Err(crate::r0::Error::Allocation))} else {
  match out {Ok(v)=>if g<4 {v.len()==n&&v[0][g]==value[g]}else{v.is_empty()},Err(_)=>false}
 };
 assert!(if cfg!(NHM_invert){!good}else{good});
}
macro_rules! gate{($name:ident,$n:expr)=>{#[kani::proof] #[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn $name(){exercise($n)}};}
'''+''.join(f'gate!(filled{i:02d},{i});\n'for i in range(6))
base='crates/aspis-core/src/'
inputs={base+'lib.rs':subprocess.check_output(['git','show','4bb3b3f:'+base+'lib.rs'],text=True).replace('#![no_std]', '#![no_std]\n#![cfg_attr(kani, feature(allocator_api))]')+'\n#[cfg(kani)] #[path="NHM_filled.rs"] mod NHM_filled;\n',base+'NHM_filled.rs':code}
patch=''
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True)
 patch+=''.join(difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n))
(E/'NHM_filled.patch').write_text(patch)
