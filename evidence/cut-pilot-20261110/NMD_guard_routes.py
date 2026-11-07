"""Safe-constructor Route B carrier calibration, not an SDK/064 certificate."""
from pathlib import Path
E=Path(__file__).resolve().parent
prefix='''use super::*;
use core::cell::{RefCell,Ref,RefMut};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
'''
for shape,guard,borrow in [('shared','Ref','borrow'),('exclusive','RefMut','borrow_mut')]:
 s=prefix+f'''
fn NMD_guard(cell:&RefCell<u8>)->{guard}<'_,u8>{{cell.{borrow}()}}
// The only write footprint of this minimal body is the real borrow token.
// It has no allocator or ambient state; no omitted footprint is claimed.
fn NMD_construct_cut(cell:&RefCell<u8>)->{guard}<'_,u8>{{cell.{borrow}()}}
fn NMD_construct_bad_value(cell:&RefCell<u8>)->{guard}<'_,u8>{{cell.replace(kani::any());cell.{borrow}()}}
fn NMD_construct_bad_token(cell:&RefCell<u8>)->{guard}<'_,u8>{{let leaked=cell.borrow();core::mem::forget(leaked);cell.{borrow}()}}
fn NMD_test<const INVERSE:bool>() {{
 let value:u8=kani::any();let cell=RefCell::new(value);
 let guard=NMD_guard(&cell);
 let exact=*guard==value && (&*guard as *const u8)==cell.as_ptr();
 assert!(exact!=INVERSE);
 drop(guard);
 assert!(cell.try_borrow_mut().is_ok(),"original cell's token is released");
}}
'''
 for name,stub,inverse in [('real',None,False),('cut','NMD_construct_cut',False),('bad_value','NMD_construct_bad_value',False),('bad_token','NMD_construct_bad_token',False),('inverse','NMD_construct_cut',True)]:
  s+='#[kani::proof]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
  if stub:s+=f'#[kani::stub(NMD_guard,{stub})]\n'
  s+=f'fn NMD_guard_{name}(){{NMD_test::<{str(inverse).lower()}>();}}\n'
 s+='''#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_copy_control(){let src:[u8;2]=kani::any();let mut dst=[0u8;2];dst.copy_from_slice(&src);assert!(dst[1]!=src[1]);}
'''
 (E/('NMD_guard_'+shape+'.rs')).write_text(s)
print('Prepared bounded free-cell guard constructor routes with value/token controls')
