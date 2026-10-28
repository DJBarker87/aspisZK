from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent
base=(E/'NCK_native.patch').read_text()
# Apply the committed initial cfg patch to a temporary frozen source image.
import tempfile
files={}
files['programs/r1-cost-probe/src/lib.rs']='''
#[cfg(kani)]
mod NCK_entry_split {
 use super::*;
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn empty(){assert_eq!(process_r1_cost_probe_instruction(&Pubkey::new_from_array(kani::any()),&[],&[]),Err(ProgramError::InvalidInstructionData));}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn empty_wrong(){assert!(process_r1_cost_probe_instruction(&Pubkey::new_from_array([0;32]),&[],&[]).is_ok());}
}
'''
files['programs/r1-cost-probe/src/r1_pool_adapter.rs']='''
#[cfg(kani)]
mod NCK_adapter_split {
 use super::*;
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn process_empty(){assert_eq!(process(&Pubkey::new_from_array(kani::any()),&[],&[]),Err(ProgramError::InvalidInstructionData));}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn process_empty_wrong(){assert!(process(&Pubkey::new_from_array([0;32]),&[],&[]).is_ok());}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn scan_short(){let data:[u8;8]=kani::any();let n:usize=kani::any();kani::assume(n<=8);assert!(matches!(scan_proof_buffer(&data[..n]),Err(ProgramError::InvalidAccountData)));}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn scan_short_wrong(){assert!(scan_proof_buffer(&[]).is_ok());}
}
'''
owned='''
#[cfg(kani)]
mod NCK_snapshot_split {
 use super::*;
 #[kani::proof] #[kani::unwind(40)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn rejected_length(){
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut l:u64=kani::any();let mut bytes:[u8;8]=kani::any();let n:usize=kani::any();kani::assume(n<=8);
  let s:bool=kani::any();let w:bool=kani::any();let e:bool=kani::any();
  let info=AccountInfo::new(&key,s,w,&mut l,&mut bytes[..n],&owner,e,0);
  let out=snapshot(&info,58295,58295);
  assert_eq!(out.length,Ok(n));assert_eq!(out.bytes,Err(ProgramError::InvalidAccountData));
  assert_eq!(out.key,key);assert_eq!(out.owner,owner);assert_eq!((out.is_signer,out.is_writable,out.executable),(s,w,e));
  assert!(info.try_borrow_mut_data().is_ok());
 }
 #[kani::proof] #[kani::unwind(40)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn rejected_length_wrong(){
  let key=Pubkey::new_from_array([0;32]);let owner=Pubkey::new_from_array([1;32]);let mut l=0;let mut bytes=[];
  let info=AccountInfo::new(&key,false,false,&mut l,&mut bytes,&owner,false,0);assert!(snapshot(&info,58295,58295).bytes.is_ok());
 }
 #[kani::proof] #[kani::unwind(40)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn borrow_conflict(){
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut l:u64=kani::any();let mut bytes:[u8;1]=kani::any();
  let info=AccountInfo::new(&key,kani::any(),kani::any(),&mut l,&mut bytes,&owner,kani::any(),0);
  let guard=info.try_borrow_mut_data().unwrap();let out=snapshot(&info,1,1);
  assert_eq!(out.length,Err(ProgramError::AccountBorrowFailed));assert_eq!(out.bytes,Err(ProgramError::AccountBorrowFailed));
  drop(guard);assert!(info.try_borrow_mut_data().is_ok());
 }
 #[kani::proof] #[kani::unwind(40)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn borrow_conflict_wrong(){
  let key=Pubkey::new_from_array([0;32]);let owner=Pubkey::new_from_array([1;32]);let mut l=0;let mut bytes=[0];
  let info=AccountInfo::new(&key,false,false,&mut l,&mut bytes,&owner,false,0);let _guard=info.try_borrow_mut_data().unwrap();assert!(snapshot(&info,1,1).bytes.is_ok());
 }
'''
# Actual seven-account SDK wrapper, fixed rejected magic: no syscall is reached.
setup='let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());\n'
for i in range(7):setup+=f'let mut l{i}:u64=kani::any();let mut d{i}=[];\n'
setup+='let accounts=['+','.join(f'AccountInfo::new(&key,false,false,&mut l{i},&mut d{i},&owner,false,0)' for i in range(7))+'];\n'
for wrong in [False,True]:
 name='header_wrong' if wrong else 'header_reject'
 prop='assert!(r.is_ok());' if wrong else 'assert_eq!(r,Err(ProgramError::InvalidInstructionData));'
 owned+=''' #[kani::proof] #[kani::unwind(40)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn '''+name+'(){'+setup+'let r=stage2(&key,&accounts,b"NOPE");'+prop+'}\n'
for wrong in [False,True]:
 name='owned_header_wrong' if wrong else 'owned_header_reject'
 prop='assert!(r.is_ok());' if wrong else 'assert_eq!(r,Err(ProgramError::InvalidInstructionData));'
 owned+=''' #[kani::proof] #[kani::unwind(40)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn '''+name+'''(){
 let accounts=core::array::from_fn::<OwnedAccount,7,_>(|_|super::NCK_owned::account());
 let r=stage2_owned(&Pubkey::new_from_array(kani::any()),&accounts,b"NOPE",Ok(kani::any()));'''+prop+'}\n'
# account() is private to its sibling: use local constructor, never change that original module.
owned=owned.replace('super::NCK_owned::account()','OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Err(ProgramError::Custom(kani::any()))}')
owned+='}\n'
files['programs/r1-cost-probe/src/r1_pool_adapter_owned.rs']=owned
# Candidate tests stay on rejecting prefixes before the seven-byte iterator.
files['crates/aspis-r1-cost-probe/src/lib.rs']='''
#[cfg(kani)]
mod NCK_kmx {include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));}
'''
cand='''
#[cfg(kani)]
mod NCK_shape {
 use super::*;
'''
for mode in ['magic','variant']:
 for wrong in [False,True]:
  name='bad_'+mode+('_wrong' if wrong else '')
  init='let mut proof=[0u8;compact::PROOF_BYTES];'
  if mode=='variant':
   for i,b in enumerate(b'R1P3CB18'):init+=f'proof[{i}]={b};'
   init+='proof[8]=255;'
  prop='assert!(parse_shape(&proof).is_ok());' if wrong else 'assert!(matches!(parse_shape(&proof),Err(Error::Parse)));'
  cand+=''' #[kani::proof] #[kani::unwind(40)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NCK_kmx::KMX_copy_nonoverlapping)]
 fn '''+name+'(){'+init+prop+'}\n'
cand+='}\n'
files['crates/aspis-r1-cost-probe/src/candidate.rs']=cand
patch=''
with tempfile.TemporaryDirectory(prefix='NCK-extend-') as d:
 for n in set(files)|set(l[6:] for l in base.splitlines() if l.startswith('+++ b/')):
  p=Path(d)/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(subprocess.check_output(['git','show','4bb3b3f5:'+n]))
 r=subprocess.run(['git','apply','-'],input=base.encode(),cwd=d,capture_output=True);assert r.returncode==0,r.stderr
 for n,append in files.items():
  old=(Path(d)/n).read_text();new=old+append
  if n=='crates/aspis-r1-cost-probe/src/lib.rs':new='#![cfg_attr(kani,feature(allocator_api))]\n'+new
  patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NCK_split.patch').write_text(patch)
