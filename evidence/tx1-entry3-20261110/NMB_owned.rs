//! Scratch-only stage1 call-boundary contract. No writable static or function pointers.
use super::*;
use std::rc::Rc;
// Fresh initialized allocation. Input havoc is available ONLY through the
// calibrated verified contract below; direct internal intrinsics are retired.
fn arbitrary_full<const N:usize>()->Vec<u8>{
 let mut v=vec![0u8;N];
 unsafe {NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;N]>());}
 v
}
fn arbitrary_bytes(n:usize)->Vec<u8>{
 match n {58295=>arbitrary_full::<58295>(),1880=>arbitrary_full::<1880>(),1768=>arbitrary_full::<1768>(),_=>unreachable!()}
}
// CLOSED343 overapproximation: metadata/error/length exact; full owned payload
// is universally arbitrary and is specialized by the child packet in Lean.
// No zero-filled logging oracle and no Ref/ProgramResult verified contract stub.
fn snapshot_oracle(a:&AccountInfo<'_>,l1:usize,l2:usize)->OwnedAccount{
 let (length,bytes)=match a.try_borrow_data(){
  Ok(d)=>{let n=d.len();(Ok(n),if n==l1||n==l2{Ok(arbitrary_bytes(n))}else{Err(ProgramError::InvalidAccountData)})},
  Err(e)=>(Err(e.clone()),Err(e)),
 };
 OwnedAccount{key:*a.key,owner:*a.owner,is_signer:a.is_signer,is_writable:a.is_writable,executable:a.executable,length,bytes}
}
fn byte_of_size(n:usize,j:usize)->u8{((n>>(8*j))&255)as u8}
fn owned_field(p:&Pubkey,a:&OwnedAccount,d:&[u8],f:usize)->u8{
 match f{0..=31=>a.key.to_bytes()[f],32..=63=>a.owner.to_bytes()[f-32],64=>a.is_signer as u8,65=>a.is_writable as u8,66=>a.executable as u8,67=>a.bytes.is_ok()as u8,68..=75=>byte_of_size(*a.length.as_ref().unwrap(),f-68),76..=107=>p.to_bytes()[f-76],108=>d[0],109=>d[1],_=>unreachable!()}
}
// Local return carrier communicates arbitrary selector and observed byte;
// no logging oracle state is global. It overapproximates the child Err arm.
fn owned_oracle(p:&Pubkey,a:&[OwnedAccount],d:&[u8])->Result<Vec<u8>,ProgramError>{
 assert_eq!(a.len(),3);assert_eq!(d.len(),2);
 let i:usize=kani::any();let f:usize=kani::any();kani::assume(i<3&&f<110);
 Err(ProgramError::Custom(((i as u32)<<16)|((f as u32)<<8)|owned_field(p,&a[i],d,f)as u32))
}
// Read-only observations of the SAME pinned SDK RefCell representation used
// by NLF's native counter receipts. No guard is acquired by a contract clause.
pub(super) fn flag(a:&AccountInfo<'_>)->*mut isize{Rc::as_ptr(&a.data).cast::<isize>() as *mut isize}
fn raw_len(a:&AccountInfo<'_>)->usize{unsafe{(&**a.data.as_ptr()).len()}}
pub(super) fn stage1_post(p:&Pubkey,a:&[AccountInfo<'_>],d:&[u8],r:&ProgramResult)->bool{
 let code=match r{Err(ProgramError::Custom(c))=>*c,_=>return false};
 let i=(code>>16)as usize;let f=((code>>8)&255)as usize;let value=code as u8;
 if i>=3||f>=110{return false}
 let n=raw_len(&a[i]);let expected=match f{
  0..=31=>a[i].key.to_bytes()[f],32..=63=>a[i].owner.to_bytes()[f-32],64=>a[i].is_signer as u8,65=>a[i].is_writable as u8,66=>a[i].executable as u8,
  67=>(n==[58295,1880,1768][i])as u8,68..=75=>byte_of_size(n,f-68),76..=107=>p.to_bytes()[f-76],108=>d[0],109=>d[1],_=>unreachable!()};
 let released=unsafe{*flag(&a[0])==0&&*flag(&a[1])==0&&*flag(&a[2])==0};
 released && if cfg!(NMB_invert){value!=expected}else{value==expected}
}
#[kani::proof_for_contract(super::stage1)]
#[kani::stub_verified(NMB_fill)]
#[kani::unwind(256)]
#[kani::stub(super::snapshot,snapshot_oracle)]
#[kani::stub(super::stage1_owned,owned_oracle)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_stage1_child_boundary(){
 let program=Pubkey::new_from_array(kani::any());
 let k0=Pubkey::new_from_array(kani::any());let k1=Pubkey::new_from_array(kani::any());let k2=Pubkey::new_from_array(kani::any());
 kani::assume(k0!=k1&&k0!=k2&&k1!=k2);
 let o0=Pubkey::new_from_array(kani::any());let o1=Pubkey::new_from_array(kani::any());let o2=Pubkey::new_from_array(kani::any());
 let mut m0:u64=kani::any();let mut m1:u64=kani::any();let mut m2:u64=kani::any();
 let mut b0=arbitrary_full::<58295>();let mut b1=arbitrary_full::<1880>();let mut b2=arbitrary_full::<1768>();
 let bases=[AccountInfo::new(&k0,kani::any(),kani::any(),&mut m0,&mut b0,&o0,kani::any(),kani::any()),AccountInfo::new(&k1,kani::any(),kani::any(),&mut m1,&mut b1,&o1,kani::any(),kani::any()),AccountInfo::new(&k2,kani::any(),kani::any(),&mut m2,&mut b2,&o2,kani::any(),kani::any())];
 let i0:usize=kani::any();let i1:usize=kani::any();let i2:usize=kani::any();kani::assume(i0<3&&i1<3&&i2<3);
 let mut a=[bases[i0].clone(),bases[i1].clone(),bases[i2].clone()];
 a[0].is_signer=kani::any();a[1].is_signer=kani::any();a[2].is_signer=kani::any();
 a[0].is_writable=kani::any();a[1].is_writable=kani::any();a[2].is_writable=kani::any();
 a[0].executable=kani::any();a[1].executable=kani::any();a[2].executable=kani::any();
 let d=if kani::any::<bool>(){[3,10]}else{[3,11]};
 super::stage1(&program,&a,&d).unwrap_err();
}
// Resource isolation for retired K001: ONE arbitrary snapshot result moved
// into the source's owned array, observed at ONE arbitrary byte. No row credit.
#[kani::proof]
#[kani::stub_verified(NMB_fill)]
#[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_array_move_window(){
 let v=arbitrary_full::<58295>();let i:usize=kani::any();kani::assume(i<58295);let before=v[i];
 let k=Pubkey::new_from_array(kani::any());let o=Pubkey::new_from_array(kani::any());
 let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();
 let proof=OwnedAccount{key:k,owner:o,is_signer:signer,is_writable:writable,executable,length:Ok(58295),bytes:Ok(v)};
 let make=||OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Err(ProgramError::AccountBorrowFailed),bytes:Err(ProgramError::AccountBorrowFailed)};
 let owned=[proof,make(),make()];let observed=owned[0].bytes.as_ref().unwrap()[i];
 if cfg!(NMB_invert){assert_ne!(observed,before)}else{assert_eq!(observed,before)}
 assert_eq!(owned[0].key,k);assert_eq!(owned[0].owner,o);assert_eq!(owned[0].is_signer,signer);assert_eq!(owned[0].is_writable,writable);assert_eq!(owned[0].executable,executable);
}

// Full fixed-array input-generation interface. Its weak contract intentionally
// permits any initialized byte value in the allocated object. This is NOT a
// contract for a frozen child and never stubs Ref/RefMut/ProgramResult.
#[kani::modifies(v)]
#[kani::ensures(|_| !cfg!(NMB_input_invert))]
fn NMB_fill<const N:usize>(v:&mut [u8;N]){let _=v;}
#[kani::modifies(v)]
#[kani::ensures(|_| true)]
fn NMB_badframe<const N:usize>(v:&mut[u8;N],frame:&mut u8){let _=v;*frame=frame.wrapping_add(1);}
#[kani::proof_for_contract(NMB_fill)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_weak_contract_58295(){let mut v=vec![0u8;58295];unsafe{NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;58295]>());}}
#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_real_58295(){let mut v=vec![0u8;58295];unsafe{NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;58295]>());}let k:usize=kani::any();kani::assume(k<58295);assert_eq!(v[k],0);}
#[kani::proof]
#[kani::stub_verified(NMB_fill)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_unimplied_58295(){let mut v=vec![0u8;58295];unsafe{NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;58295]>());}let k:usize=kani::any();kani::assume(k<58295);assert_eq!(v[k],0);}
#[kani::proof_for_contract(NMB_badframe)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_badframe_58295(){let mut v=vec![0u8;58295];let mut f:u8=kani::any();unsafe{NMB_badframe(&mut *v.as_mut_ptr().cast::<[u8;58295]>(),&mut f);}}
#[kani::proof_for_contract(NMB_fill)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_weak_contract_1880(){let mut v=vec![0u8;1880];unsafe{NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;1880]>());}}
#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_real_1880(){let mut v=vec![0u8;1880];unsafe{NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;1880]>());}let k:usize=kani::any();kani::assume(k<1880);assert_eq!(v[k],0);}
#[kani::proof]
#[kani::stub_verified(NMB_fill)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_unimplied_1880(){let mut v=vec![0u8;1880];unsafe{NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;1880]>());}let k:usize=kani::any();kani::assume(k<1880);assert_eq!(v[k],0);}
#[kani::proof_for_contract(NMB_badframe)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_badframe_1880(){let mut v=vec![0u8;1880];let mut f:u8=kani::any();unsafe{NMB_badframe(&mut *v.as_mut_ptr().cast::<[u8;1880]>(),&mut f);}}
#[kani::proof_for_contract(NMB_fill)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_weak_contract_1768(){let mut v=vec![0u8;1768];unsafe{NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;1768]>());}}
#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_real_1768(){let mut v=vec![0u8;1768];unsafe{NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;1768]>());}let k:usize=kani::any();kani::assume(k<1768);assert_eq!(v[k],0);}
#[kani::proof]
#[kani::stub_verified(NMB_fill)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_unimplied_1768(){let mut v=vec![0u8;1768];unsafe{NMB_fill(&mut *v.as_mut_ptr().cast::<[u8;1768]>());}let k:usize=kani::any();kani::assume(k<1768);assert_eq!(v[k],0);}
#[kani::proof_for_contract(NMB_badframe)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_input_badframe_1768(){let mut v=vec![0u8;1768];let mut f:u8=kani::any();unsafe{NMB_badframe(&mut *v.as_mut_ptr().cast::<[u8;1768]>(),&mut f);}}
// Loop-free call-boundary fragments. Each copies the frozen source expressions
// and has an EMPTY modifies set. These do not allocate, borrow SDK cells, or
// inspect any payload; earlier owned buffers therefore stay in the full frame.
#[kani::requires(data.len()==2)]
#[kani::modifies()]
#[kani::ensures(|r| if cfg!(NMB_invert){*r != !(data[0]==3&&(data[1]==10||data[1]==11)&&count==3)}else{*r == !(data[0]==3&&(data[1]==10||data[1]==11)&&count==3)})]
fn NMB_guard_fragment(data:&[u8],count:usize)->bool {!(data==&[3,10]||data==&[3,11])||count!=3}
#[kani::proof_for_contract(NMB_guard_fragment)]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_guard_fragment_contract(){let d:[u8;2]=kani::any();NMB_guard_fragment(&d,kani::any());}
#[derive(Clone,Copy)]
struct NMB_Args {account:usize,length1:usize,length2:usize}
fn NMB_size(i:usize)->usize{match i{0=>POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES+verifier::PROOF_BYTES,1=>POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES,2=>CHECKPOINT_TAIL_BYTES,_=>unreachable!()}}
#[kani::requires(accounts.len()==3 && I<3)]
#[kani::modifies()]
#[kani::ensures(|r| r.account == (&accounts[if cfg!(NMB_invert){(I+1)%3}else{I}]as*const AccountInfo as usize) && r.length1==NMB_size(I) && r.length2==NMB_size(I))]
fn NMB_snapshot_args<const I:usize>(accounts:&[AccountInfo<'_>])->NMB_Args{
 let account=&accounts[I];let length=match I{0=>POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES+verifier::PROOF_BYTES,1=>POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES,2=>CHECKPOINT_TAIL_BYTES,_=>unreachable!()};
 NMB_Args{account:account as *const AccountInfo as usize,length1:length,length2:length}
}
fn NMB_args_harness<const I:usize>(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut money:u64=kani::any();let mut bytes:[u8;1]=kani::any();
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut money,&mut bytes,&owner,kani::any(),kani::any());
 let mut accounts=[a.clone(),a.clone(),a];
 accounts[0].is_writable=kani::any();accounts[1].is_writable=kani::any();accounts[2].is_writable=kani::any();
 accounts[0].is_signer=kani::any();accounts[1].is_signer=kani::any();accounts[2].is_signer=kani::any();
 accounts[0].executable=kani::any();accounts[1].executable=kani::any();accounts[2].executable=kani::any();
 NMB_snapshot_args::<I>(&accounts);
}
#[kani::proof_for_contract(NMB_snapshot_args)]
#[kani::unwind(64)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_snapshot0_args_contract(){NMB_args_harness::<0>()}
#[kani::proof_for_contract(NMB_snapshot_args)]
#[kani::unwind(64)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_snapshot1_args_contract(){NMB_args_harness::<1>()}
#[kani::proof_for_contract(NMB_snapshot_args)]
#[kani::unwind(64)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_snapshot2_args_contract(){NMB_args_harness::<2>()}
// Isolate the old allocation's FRAME from the large variable-index read.
// No byte element is read by the positive fragment or its postcondition.
#[derive(Clone,Copy,PartialEq,Eq)]
struct NMB_Header {key:[u8;32],owner:[u8;32],signer:bool,writable:bool,executable:bool,length:usize,bytes_ok:bool,ptr:usize,len:usize,cap:usize}
fn NMB_header(a:&OwnedAccount)->NMB_Header{
 let (ok,ptr,len,cap)=match &a.bytes{Ok(v)=>(true,v.as_ptr()as usize,v.len(),v.capacity()),Err(_)=>(false,0,0,0)};
 NMB_Header{key:a.key.to_bytes(),owner:a.owner.to_bytes(),signer:a.is_signer,writable:a.is_writable,executable:a.executable,length:*a.length.as_ref().unwrap(),bytes_ok:ok,ptr,len,cap}
}
#[kani::requires(proof.length.is_ok() && public.length.is_ok() && checkpoint.length.is_ok())]
#[kani::modifies()]
#[kani::ensures(|out| (NMB_header(&out[0])==old(NMB_header(&proof))) != cfg!(NMB_invert) && NMB_header(&out[1])==old(NMB_header(&public)) && NMB_header(&out[2])==old(NMB_header(&checkpoint)))]
fn NMB_array_header(mut proof:OwnedAccount,public:OwnedAccount,checkpoint:OwnedAccount)->[OwnedAccount;3]{
 if cfg!(NMB_array_badframe){if let Ok(v)=&mut proof.bytes{v[0]=v[0].wrapping_add(1);}}
 let owned=[proof,public,checkpoint];owned
}
fn NMB_header_input<const N:usize>()->OwnedAccount{
 let bytes=if kani::any::<bool>(){Ok(arbitrary_full::<N>())}else{Err(ProgramError::InvalidAccountData)};
 OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes}
}
#[kani::proof_for_contract(NMB_array_header)]
#[kani::stub_verified(NMB_fill)]
#[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_array_header_contract(){NMB_array_header(NMB_header_input::<58295>(),NMB_header_input::<1880>(),NMB_header_input::<1768>());}
// Discriminant supplement to the header/no-write cut. The input domain is the
// actual normal snapshot domain: Ok(Vec) or deferred InvalidAccountData.
#[kani::proof]
#[kani::stub_verified(NMB_fill)]
#[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_array_error_contract(){
 let a=NMB_header_input::<58295>();let b=NMB_header_input::<1880>();let c=NMB_header_input::<1768>();
 let e0=a.bytes.is_ok();let e1=b.bytes.is_ok();let e2=c.bytes.is_ok();
 let out=NMB_array_header(a,b,c);
 let valid=|i:usize,was_ok:bool|if was_ok{out[i].bytes.is_ok()}else{matches!(out[i].bytes,Err(ProgramError::InvalidAccountData))};
 let first=valid(0,e0);if cfg!(NMB_invert){assert!(!first)}else{assert!(first)}
 assert!(valid(1,e1));assert!(valid(2,e2));
}
#[kani::requires(accounts.len()==3)]
#[kani::modifies()]
#[kani::ensures(|r| r[0]==(&accounts[if cfg!(NMB_invert){1}else{0}]as*const OwnedAccount as usize) && r[1]==(&accounts[1]as*const OwnedAccount as usize) && r[2]==(&accounts[2]as*const OwnedAccount as usize))]
fn NMB_owned_select(accounts:&[OwnedAccount])->[usize;3]{
 let proof_account=&accounts[0];let public_account=&accounts[1];let checkpoint_account=&accounts[2];
 let refs=[proof_account,public_account,checkpoint_account];
 [refs[0]as*const OwnedAccount as usize,refs[1]as*const OwnedAccount as usize,refs[2]as*const OwnedAccount as usize]
}
#[kani::proof_for_contract(NMB_owned_select)]
#[kani::stub_verified(NMB_fill)]
#[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_owned_select_contract(){let a=[NMB_header_input::<58295>(),NMB_header_input::<1880>(),NMB_header_input::<1768>()];NMB_owned_select(&a);}
#[derive(Clone,Copy)]
struct NMB_Span {ok:bool,end:usize,invalid_data:bool}
#[kani::modifies()]
#[kani::ensures(|r| r.ok == (((proof_start as u128)+(proof_length as u128)<=usize::MAX as u128) != cfg!(NMB_invert)) && r.end == (if (proof_start as u128)+(proof_length as u128)<=usize::MAX as u128{((proof_start as u128)+(proof_length as u128))as usize}else{0}) && r.invalid_data == !r.ok)]
fn NMB_checked_span(proof_start:usize,proof_length:usize)->NMB_Span{
 let result=proof_start.checked_add(proof_length).ok_or(ProgramError::InvalidAccountData);
 match result{Ok(end)=>NMB_Span{ok:true,end,invalid_data:false},Err(e)=>NMB_Span{ok:false,end:0,invalid_data:e==ProgramError::InvalidAccountData}}
}
#[kani::proof_for_contract(NMB_checked_span)]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_checked_span_contract(){NMB_checked_span(kani::any(),kani::any());}
#[kani::requires(data==&[3,10] || data==&[3,11])]
#[kani::modifies()]
#[kani::ensures(|r| *r==(true,if cfg!(NMB_invert){2}else{1}))]
fn NMB_dispatch_fragment(data:&[u8])->(bool,u8){
 let admitted=crate::pool_route::admitted(data);
 let route=match data.first().copied(){Some(4)=>4,Some(5)=>5,Some(6)=>6,_ if data==&[3,10]||data==&[3,11]=>1,_=>2};
 (admitted,route)
}
#[kani::proof_for_contract(NMB_dispatch_fragment)]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMB_native::KMX_copy_nonoverlapping)]
fn NMB_dispatch_fragment_contract(){let d=if kani::any::<bool>(){[3,10]}else{[3,11]};NMB_dispatch_fragment(&d);}
