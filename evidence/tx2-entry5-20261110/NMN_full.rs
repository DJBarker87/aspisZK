// Original-buffer parent experiment. Not a full241 certificate.
include!("NMN_format.rs");
struct NMN_FullLog {
 mode:u8,fault:u8,stage:u8,program:*const Pubkey,accounts:*const OwnedAccount,
 data:*const u8,data_len:usize,slot:u64,proof:*const u8,checkpoint:*const u8,
 statement:*const PoolV1PairForestTerminalStatementV1,
 public:core::mem::MaybeUninit<[u8;1880]>,format:core::mem::MaybeUninit<PoolV1PairForestTerminalFormatErrorV1>,
 reply:NMN_ErrorSig,emit_ok:bool,
}
#[repr(C)]
struct NMN_FullKey{key:Pubkey,log:UnsafeCell<NMN_FullLog>}
unsafe fn NMN_full_context(ptr:*const u8)->*const NMN_FullKey{unsafe{NMN_owner(ptr).cast()}}
#[repr(C)]
struct NMN_Tail {owner:UnsafeCell<*mut ()>,marker:u8}
fn NMN_buffer<const N:usize>(owner:*mut ())->Vec<u8>{
 // Safe Box allocation, then exact Vec layout/capacity; the LOCAL log lives
 // only in spare capacity, outside every shared logical byte slice.
 if N==58295{
  let bytes:[u8;58312]=kani::any();let marker=bytes[16];let b=Box::new(bytes);let p=Box::into_raw(b).cast::<u8>();
  unsafe{p.add(58296).cast::<NMN_Tail>().write(NMN_Tail{owner:UnsafeCell::new(owner),marker});Vec::from_raw_parts(p,N,58312)}
 }else{
  assert_eq!(N,1768);let bytes:[u8;1784]=kani::any();let marker=bytes[16];let b=Box::new(bytes);let p=Box::into_raw(b).cast::<u8>();
  unsafe{p.add(1768).cast::<NMN_Tail>().write(NMN_Tail{owner:UnsafeCell::new(owner),marker});Vec::from_raw_parts(p,N,1784)}
 }
}
unsafe fn NMN_tail(p:*const u8,n:usize)->*const NMN_Tail{
 let offset=if n==58295{58296}else{assert_eq!(n,1768);1768};unsafe{p.add(offset).cast()}
}
unsafe fn NMN_buffer_context(p:*const u8,n:usize)->*const NMN_FullKey{
 unsafe{(*(*NMN_tail(p,n)).owner.get()).cast()}
}

fn NMN_full_validate(program:&Pubkey,accounts:&[OwnedAccount],data:&[u8],slot:Result<u64,PE>)->Result<ValidatedAsqa,PE>{
 let ctx=program as *const Pubkey as *const NMN_FullKey;let s=unsafe{&mut *(*ctx).log.get()};
 assert_eq!(program as *const Pubkey,s.program);assert_eq!(accounts.as_ptr(),s.accounts);assert_eq!(accounts.len(),7);
 assert_eq!(data.as_ptr(),s.data);assert_eq!(data.len(),s.data_len);assert_eq!(slot.unwrap(),s.slot);assert_eq!(s.stage,0);
 if s.fault!=3{s.stage=1;}
 let value=NMN_statement_variant(kani::any());let layout=Layout::new::<PoolV1PairForestTerminalStatementV1>();
 let p=unsafe{NMN_ALLOCATOR.alloc(layout)};if p.is_null(){std::alloc::handle_alloc_error(layout);}
 let typed=p.cast::<PoolV1PairForestTerminalStatementV1>();unsafe{typed.write(value);NMN_set_owner(p,ctx.cast_mut().cast());}
 s.statement=typed;
 let proof_length=if s.mode==0{let n:usize=kani::any();kani::assume(688usize.checked_add(n).is_none());n}
 else if s.mode==1{let n:usize=kani::any();kani::assume(matches!(688usize.checked_add(n),Some(x) if x!=58295));n}
 else{57607};
 Ok(ValidatedAsqa{statement:unsafe{Box::from_raw(typed)},proof_length})
}
fn NMN_full_getter(account:&OwnedAccount)->Result<&[u8],PE>{
 let bytes=match &account.bytes{Ok(b)=>b,Err(_)=>panic!("input constructor must retain Ok")};
 assert!(!bytes.is_empty(),"only original proof/checkpoint getters entered");
 let ctx=unsafe{NMN_buffer_context(bytes.as_ptr(),bytes.len())};let s=unsafe{&mut *(*ctx).log.get()};
 let (index,ptr,len)=if s.stage==1{(0,s.proof,58295)}else{assert_eq!(s.stage,2);(6,s.checkpoint,1768)};
 assert_eq!(account as *const OwnedAccount,unsafe{s.accounts.add(index)});
 assert_eq!(bytes.as_ptr(),ptr);assert_eq!(bytes.len(),len);s.stage+=1;
 // Exact CLOSED getter replay here, not a claimed full-type borrowed oracle.
 Ok(bytes)
}
fn NMN_full_encoder(statement:&PoolV1PairForestTerminalStatementV1)->Result<[u8;1880],PoolV1PairForestTerminalFormatErrorV1>{
 let ctx=unsafe{NMN_full_context((statement as *const PoolV1PairForestTerminalStatementV1).cast())};let s=unsafe{&mut *(*ctx).log.get()};
 assert_eq!(s.stage,3);assert_eq!(statement as *const PoolV1PairForestTerminalStatementV1,s.statement);s.stage=4;
 if s.mode==2{let error=NMN_any_PoolV1PairForestTerminalFormatErrorV1();s.format.write(error);Err(error)}
 else{let bytes:[u8;1880]=kani::any();s.public.write(bytes);Ok(bytes)}
}
fn NMN_full_auth<H:aspis_core::Digest32>(public:&[u8],proof:&[u8],checkpoint:&[u8],_hash:H,_obs:verifier::Observer)->Result<(),verifier::Error>{
 let base=unsafe{proof.as_ptr().sub(688)};let ctx=unsafe{NMN_buffer_context(base,58295)};let s=unsafe{&mut *(*ctx).log.get()};
 assert_eq!(s.stage,4);assert_eq!(base,s.proof);assert_eq!(proof.len(),57607);assert_eq!(checkpoint.as_ptr(),s.checkpoint);assert_eq!(checkpoint.len(),1768);assert_eq!(public.len(),1880);
 let i:usize=kani::any();kani::assume(i<1880);let encoded=unsafe{s.public.assume_init_ref()};
 assert_eq!(public[i],encoded[i],"encoder byte at arbitrary public offset");s.stage=5;
 if s.mode==3{Err(verifier::Error::Parse)}else{Ok(())}
}
fn NMN_full_error(e:verifier::Error)->PE{
 // Finite Parse partition only; general callback transport remains OPEN.
 assert!(matches!(e,verifier::Error::Parse));PE::InvalidInstructionData
}
fn NMN_full_emit(statement:&PoolV1PairForestTerminalStatementV1)->ProgramResult{
 let ctx=unsafe{NMN_full_context((statement as *const PoolV1PairForestTerminalStatementV1).cast())};let s=unsafe{&mut *(*ctx).log.get()};
 assert_eq!(s.stage,5);assert_eq!(statement as *const PoolV1PairForestTerminalStatementV1,s.statement);s.stage=6;
 let ok:bool=kani::any();s.emit_ok=ok;if ok{Ok(())}else{let t:u8=kani::any();kani::assume(t<26 && t!=14);let e=NMN_error_tag(t);s.reply=NMN_sig(&e);Err(e)}
}
fn NMN_full_parent<const MODE:u8,const FAULT:u8>(){
 let zero=NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0};
 let key=NMN_FullKey{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(NMN_FullLog{mode:MODE,fault:FAULT,stage:0,program:core::ptr::null(),accounts:core::ptr::null(),data:core::ptr::null(),data_len:320,slot:kani::any(),proof:core::ptr::null(),checkpoint:core::ptr::null(),statement:core::ptr::null(),public:core::mem::MaybeUninit::uninit(),format:core::mem::MaybeUninit::uninit(),reply:zero,emit_ok:false})};
 let owner=(&key as *const NMN_FullKey).cast_mut().cast();
 let mut input=core::mem::MaybeUninit::<[OwnedAccount;7]>::uninit();
 for i in 0..7{
  let a=unsafe{input.as_mut_ptr().cast::<OwnedAccount>().add(i)};
  let bytes=if i==0{NMN_buffer::<58295>(owner)}else if i==6{NMN_buffer::<1768>(owner)}else{Vec::new()};
  unsafe{
   if i==0{(*key.log.get()).proof=bytes.as_ptr();}if i==6{(*key.log.get()).checkpoint=bytes.as_ptr();}
   core::ptr::addr_of_mut!((*a).key).write(Pubkey::new_from_array(kani::any()));core::ptr::addr_of_mut!((*a).owner).write(Pubkey::new_from_array(kani::any()));
   core::ptr::addr_of_mut!((*a).is_signer).write(kani::any());core::ptr::addr_of_mut!((*a).is_writable).write(kani::any());core::ptr::addr_of_mut!((*a).executable).write(kani::any());
   core::ptr::addr_of_mut!((*a).length).write(Ok(kani::any()));core::ptr::addr_of_mut!((*a).bytes).write(Ok(bytes));
  }
 }
 // All fields initialized; borrow in place without a non-Copy array move.
 let accounts=unsafe{input.assume_init_ref()};let mut data:[u8;320]=kani::any();data[0]=b'A';data[1]=b'S';data[2]=b'Q';data[3]=b'8';
 let slot;unsafe{let s=&mut *key.log.get();s.program=&key.key;s.accounts=accounts.as_ptr();s.data=if FAULT==1{data.as_ptr().add(1)}else{data.as_ptr()};slot=s.slot;}
 let result=stage2_owned(&key.key,accounts,&data,Ok(slot));let s=unsafe{&*key.log.get()};
 let expected_stage=if MODE<=1{3}else if MODE==2{4}else if MODE==3{5}else{6};assert_eq!(s.stage,expected_stage,"ordered parent call prefix");
 if FAULT==2{assert_eq!(result.is_ok(),MODE!=4 || !s.emit_ok,"ignored reply control");return;}
 if MODE<=1{assert_eq!(result,Err(PE::InvalidAccountData));}else if MODE<=3{assert_eq!(result,Err(PE::InvalidInstructionData));}
 else{match result{Ok(())=>assert!(s.emit_ok),Err(e)=>{assert!(!s.emit_ok);NMN_same(NMN_sig(&e),s.reply);}}}
}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_0_pass(){NMN_full_parent::<0,0>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_0_argument(){NMN_full_parent::<0,1>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_0_reply(){NMN_full_parent::<0,2>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_0_write(){NMN_full_parent::<0,3>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_1_pass(){NMN_full_parent::<1,0>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_1_argument(){NMN_full_parent::<1,1>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_1_reply(){NMN_full_parent::<1,2>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_1_write(){NMN_full_parent::<1,3>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_2_pass(){NMN_full_parent::<2,0>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_2_argument(){NMN_full_parent::<2,1>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_2_reply(){NMN_full_parent::<2,2>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_2_write(){NMN_full_parent::<2,3>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_3_pass(){NMN_full_parent::<3,0>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_3_argument(){NMN_full_parent::<3,1>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_3_reply(){NMN_full_parent::<3,2>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_3_write(){NMN_full_parent::<3,3>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_4_pass(){NMN_full_parent::<4,0>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_4_argument(){NMN_full_parent::<4,1>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_4_reply(){NMN_full_parent::<4,2>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(validate_asq8,NMN_full_validate)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_full_getter)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_full_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_full_auth)]
#[kani::stub(emit_result,NMN_full_emit)]#[kani::stub(crate::error,NMN_full_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_full_4_write(){NMN_full_parent::<4,3>();}

fn NMN_buffer_probe<const N:usize,const BAD:bool>(){
 let mut cell=0u8;let owner=(&mut cell as *mut u8).cast();let v=NMN_buffer::<N>(owner);
 assert_eq!(v.len(),N);assert!(v.capacity()>=N+8);
 let tail=unsafe{&*NMN_tail(v.as_ptr(),N)};assert_eq!(unsafe{*tail.owner.get()},owner);
 assert_eq!(v[16],if BAD{tail.marker^1}else{tail.marker},"initialized byte at fixed buffer window");
}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_buffer_proof(){NMN_buffer_probe::<58295,false>();}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_buffer_proof_control(){NMN_buffer_probe::<58295,true>();}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_buffer_checkpoint(){NMN_buffer_probe::<1768,false>();}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_buffer_checkpoint_control(){NMN_buffer_probe::<1768,true>();}
