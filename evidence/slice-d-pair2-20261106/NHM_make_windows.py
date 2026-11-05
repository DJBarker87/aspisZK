from pathlib import Path
import subprocess,difflib,json
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/'
code=r'''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy,PartialEq,Debug)]struct Dot{words:[u64;8],count:usize}
struct Log{field_index:usize,ptr:*const u8,len:usize,field_value:[u32;8],left:[u32;8],right:[u32;4],before:Dot,after:Dot,fail:bool,calls:usize}
fn field(f:&[u8],i:usize,l:&mut Log)->[u32;8]{l.field_index=i;l.ptr=f.as_ptr();l.len=f.len();l.field_value}
fn push(d:&mut Dot,x:[u32;8],y:[u32;4],l:&mut Log)->Result<(),()>{l.left=x;l.right=y;l.before=*d;*d=l.after;l.calls+=1;if l.fail{Err(())}else{Ok(())}}
fn partial_window(f:&[u8],common:&[[u32;4];16],s:usize,j:usize,d:&mut Dot,l:&mut Log)->Result<(),Error>{
 let x=field(f,16*s+j,l);match push(d,x,common[j],l){Ok(())=>{},Err(_)=>return Err(Error::Parse)}Ok(())
}
fn byte_window(f:&[u8],scratch:&[[u32;4]],j:usize,d:&mut Dot,l:&mut Log)->Result<(),Error>{
 let x=field(f,j,l);match push(d,x,scratch[j],l){Ok(())=>{},Err(_)=>return Err(Error::Parse)}Ok(())
}
fn high_window(partials:&[[u32;8];4],coeffs:&[[u32;4];4],j:usize,d:&mut Dot,l:&mut Log)->Result<(),Error>{
 match push(d,partials[j],coeffs[j],l){Ok(())=>{},Err(_)=>return Err(Error::Parse)}Ok(())
}
fn exercise(family:usize,g:usize){
 let common:[[u32;4];16]=kani::any();let scratch:[[u32;4];64]=kani::any();let high:[[u32;8];4]=kani::any();let coeffs:[[u32;4];4]=kani::any();
 let s:usize=kani::any();kani::assume(s<4);let j:usize=kani::any();kani::assume(j<if family==2{4}else if family==1{64}else{16});
 let before=Dot{words:kani::any(),count:kani::any()};let after=Dot{words:kani::any(),count:kani::any()};
 let bytes:[u8;2048]=kani::any();let x:[u32;8]=kani::any();let fail:bool=kani::any();let mut d=before;
 let mut l=Log{field_index:999,ptr:core::ptr::null(),len:0,field_value:x,left:[0;8],right:[0;4],before,after,fail,calls:0};
 let r=if family==0{partial_window(&bytes,&common,s,j,&mut d,&mut l)}else if family==1{byte_window(&bytes,&scratch,j,&mut d,&mut l)}else{high_window(&high,&coeffs,j,&mut d,&mut l)};
 let good=match g{
 0=>l.left==if family==2{high[j]}else{x},
 1=>l.right==if family==2{coeffs[j]}else if family==1{scratch[j]}else{common[j]},
 2=>l.before==before,
 3=>d==after,
 4=>r.is_err()==fail,
 5=>l.calls==1,
 6=>l.field_index==if family==0{16*s+j}else{j},
 7=>l.ptr==bytes.as_ptr()&&l.len==2048,
 _=>false};
 assert!(if cfg!(NHM_invert){!good}else{good});
}
macro_rules! gate{($name:ident,$family:expr,$n:expr)=>{#[kani::proof]#[kani::unwind(2050)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){exercise($family,$n)}};}
'''
for fam,name,groups in [(0,'partial',8),(1,'byte',8),(2,'high',6)]:
 code+=''.join(f'gate!({name}{g:02d},{fam},{g});\n'for g in range(groups))
inputs=json.loads((E.parent/'slice-d-finish-20261105/NGM_NATIVE_INPUTS.json').read_text());inputs[C+'NHM_windows.rs']=code
inputs[C+'weights.rs']+='\n#[cfg(kani)] #[path="NHM_windows.rs"] mod NHM_windows;\n'
patch=''
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True)
 patch+=''.join(difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n))
(E/'NHM_windows.patch').write_text(patch)
