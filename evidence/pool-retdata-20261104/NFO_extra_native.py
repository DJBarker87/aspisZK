"""Per-field false-reply controls, exact KMX step, and constructor ownership."""
from pathlib import Path
import json,sys,subprocess,difflib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';mode=sys.argv[1]
original=json.loads((E/'NFO_K007-shape.json').read_text())['source']
if mode.startswith('field-'):
 field=mode.removeprefix('field-');assert field in ['kind','master','selected','lane','nullifier','index','root','frontier']
 mutate={'kind':'changed.transition_kind=match changed.transition_kind{PoolV1TransitionKind::PrivateTransfer=>PoolV1TransitionKind::Withdrawal,_=>PoolV1TransitionKind::PrivateTransfer};','master':'changed.master_account[frame.j%32]^=1;','selected':'changed.selected_lane_account[frame.j%32]^=1;','lane':'changed.output_lane^=1;','nullifier':'changed.nullifier[frame.j%8].0^=1;','index':'changed.verified_afterstate.next_pair_index^=1;','root':'changed.verified_afterstate.next_root[frame.j%8].0^=1;','frontier':'changed.verified_afterstate.next_frontier[frame.j%20][frame.j%8].0^=1;'}[field]
 source=original.replace('value: Box::new(result)','value: Box::new({let mut changed=result;'+mutate+'changed})')
else:
 helpers=original[original.index('fn digest()'):original.index('struct Runtime {')]
 source='use super::*;\nuse aspis_statement::pool_v1::*;\nuse aspis_core::field::M31;\n'+helpers
 if mode.startswith('window'):
  source+=r'''
fn step(ptr:*const u8,out:*mut u8,old_size:usize,new_size:usize,i:&mut usize){
 if *i<core::cmp::min(old_size,new_size){
  let value=unsafe{ptr.cast::<core::mem::MaybeUninit<u8>>().add(*i).read()};
  unsafe{out.cast::<core::mem::MaybeUninit<u8>>().add(*i).write(value)};*i+=1;
 }
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
fn association(){
 let src:[u8;792]=kani::any();let mut dst:[u8;792]=kani::any();let old_size:usize=kani::any();kani::assume(old_size>=792);
 let mut i:usize=kani::any();let before_i=i;let j:usize=kani::any();kani::assume(j<792);let before=dst[j];let src_before=src[j];
 let value=Box::new(result());let family:u8=kani::any();kani::assume(family<8);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);let index:usize=kani::any();kani::assume(index<32);let field=observe(&value,family,row,word,index);
 step(src.as_ptr(),dst.as_mut_ptr(),old_size,792,&mut i);
 assert!(i==if before_i<792{before_i+1}else{before_i});
 assert!(dst[j]==if before_i<792&&j==before_i{src[j]}else{before});
 assert!(src[j]==src_before&&observe(&value,family,row,word,index)==field);
}
'''
  if mode=='window-byte':source=source.replace('.write(value)', '.write(core::mem::MaybeUninit::new(value.assume_init()^1))')
  if mode=='window-frame':source=source.replace('out.cast::<core::mem::MaybeUninit<u8>>().add(*i)','out.cast::<core::mem::MaybeUninit<u8>>().add((*i+1)%792)')
 elif mode.startswith('box'):
  source+=r'''
struct Frame{allocated:*const PoolV1PairForestTerminalResultV1}
fn native(r:PoolV1PairForestTerminalResultV1,f:&mut Frame)->Box<PoolV1PairForestTerminalResultV1>{
 let b=Box::new(r);f.allocated=&*b;b
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
fn association(){
 let original=result();let raw:[u8;792]=kani::any();let data=Box::new(raw);let ptr=data.as_ptr();
 let family:u8=kani::any();kani::assume(family<8);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);let index:usize=kani::any();kani::assume(index<32);
 let mut frame=Frame{allocated:core::ptr::null()};let out=native(original,&mut frame);
 assert!(core::ptr::eq(&*out,frame.allocated));
 assert!(!core::ptr::eq((&*out as *const PoolV1PairForestTerminalResultV1).cast::<u8>(),ptr));
 assert!(observe(&out,family,row,word,index)==observe(&original,family,row,word,index));
 let j:usize=kani::any();kani::assume(j<792);assert!(data[j]==raw[j]);
}
'''
  if mode=='box-value':source=source.replace('let b=Box::new(r);','let mut r=r;r.output_lane^=1;let b=Box::new(r);')
  if mode=='box-allocation':source=source.replace('f.allocated=&*b;b','f.allocated=&*b;let other=Box::new(*b);drop(b);other')
 else:raise AssertionError(mode)
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 frozen=subprocess.check_output(['git','show',REV+':'+p],text=True)
 hook=frozen+'\n#[cfg(kani)]\n#[path="NFO_read.rs"]\nmod NFO_read;\n' if p.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFO_read.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
(E/'NFO_native.patch').write_text(patch);(E/'NFO_CURRENT.json').write_text(json.dumps(dict(mode=mode,source=source,classification='false-field control' if mode.startswith('field') else 'one actual KMX reallocation iteration; allocation validity/ownership retained' if mode.startswith('window') else 'actual Box constructor same-allocation/value/freshness cut; caller association remains separate'),indent=1)+'\n')
