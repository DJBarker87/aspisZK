"""Descriptor-wide rejection/selected-bump observations; sparse payload domain explicit."""
from pathlib import Path
import subprocess,sys,json,difflib
E=Path(__file__).resolve().parent;mode,kind=sys.argv[1:];assert mode in ['positive','negative'] and kind in ['master','checkpoint','stored','storedbusy']
code='''use super::*;
#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NHP_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NHP_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NHP_KMX::KMX_realloc)]
fn association(){
 let n:usize=kani::any();kani::assume(n<=isize::MAX as usize);
 let layout=core::alloc::Layout::from_size_align(n.max(1),1).unwrap();let pointer=unsafe{alloc::alloc::alloc_zeroed(layout)};kani::assume(!pointer.is_null());
 let index:usize=kani::any();kani::assume(if n==0 {index==0}else{index<n&&index<96});let byte:u8=kani::any();if n>0 {unsafe{pointer.add(index).write(byte);}}
 let before=if n>0 {unsafe{pointer.add(index).read()}}else{0};
 let key=Pubkey::new_from_array(kani::any());let program=Pubkey::new_from_array(kani::any());let master=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let old_lamports=lamports;
 {
 let data=unsafe{core::slice::from_raw_parts_mut(pointer,n)};
 let account=AccountInfo::new(&key,false,false,&mut lamports,data,&program,false,kani::any());
 BODY
 assert!(account.data.borrow().len()==n);assert!(account.data.borrow().as_ptr()==pointer);assert!(**account.lamports.borrow()==old_lamports);
 if n>0 {assert!(account.data.borrow()[index]==before);}
 assert!(account.try_borrow_mut_data().is_ok());assert!(alloc::rc::Rc::strong_count(&account.data)==1);
 }
 unsafe{alloc::alloc::dealloc(pointer,layout);}
}
'''
if kind in ['master','checkpoint']:
 constant='POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES' if kind=='master' else 'POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES'
 call='decode_terminal_master_box_v1(&program,&account)' if kind=='master' else 'decode_terminal_checkpoint_box_v1(&program,&master,&account)'
 body=f'kani::assume(n!={constant});let returned=super::{call}.err();\n'
 body+='assert!(returned==Some('+('ProgramError::InvalidArgument' if mode=='negative' else 'PoolV1ProgramError::InvalidAccountType.into()')+'));\n'
elif kind=='stored':
 body='let expected=if n==POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES {Some(unsafe{pointer.add(72).read()})}else{None};let returned=super::stored_lane_bump(&account).unwrap();\n'
 body+='assert!(returned'+('!=' if mode=='negative' else '==')+'expected);\n'
else:
 body='let held=account.try_borrow_mut_data().unwrap();let returned=super::stored_lane_bump(&account).err();drop(held);\n'
 body+='assert!(returned==Some('+('ProgramError::InvalidArgument' if mode=='negative' else 'ProgramError::AccountBorrowFailed')+'));\n'
source=code.replace('BODY',body);rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True);patch=''
for p in ['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/lib.rs']:
 before=read(p);after=before+'\n#[cfg(kani)]\nmod NHP_dynamic_accounts {\n'+source+'}\n' if p.endswith('/pair_forest.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+before+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NHP_KMX;\n'
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NHP_native.patch').write_text(patch);(E/'NHP_CURRENT.json').write_text(json.dumps(dict(kind='dynamic account '+kind,mode=mode,source=source,domain='Every returning valid allocation length0..isize::MAX; otherwise-zero storage with one arbitrary byte in first min(n,96) positions; initial SDK data counter0 or live exclusive guard; wrong-length class or exact selected bump class',modifies=[],production_credit=False,remaining='arbitrary full heap contents/aliases/borrow states, physical runtime entry relation, actual decoder/PDA success packets; no sparse payload premise adopted'),indent=1)+'\n')
print('pair_forest::NHP_dynamic_accounts::association')
