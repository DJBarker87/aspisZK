use super::*;
use core::cell::UnsafeCell;
include!("NMN_statement.rs");
include!("NMN_heap.rs");
use solana_program::program_error::ProgramError as PE;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy,Debug,PartialEq)]
struct NMN_ErrorSig { tag:u8,custom:u32,ptr:*const u8,len:usize,cap:usize }
fn NMN_sig(e:&PE)->NMN_ErrorSig {
 let (tag,custom,ptr,len,cap)=match e {
  PE::Custom(x)=>(0,*x,core::ptr::null(),0,0),
  PE::InvalidArgument=>(1,0,core::ptr::null(),0,0),
  PE::InvalidInstructionData=>(2,0,core::ptr::null(),0,0),
  PE::InvalidAccountData=>(3,0,core::ptr::null(),0,0),
  PE::AccountDataTooSmall=>(4,0,core::ptr::null(),0,0),
  PE::InsufficientFunds=>(5,0,core::ptr::null(),0,0),
  PE::IncorrectProgramId=>(6,0,core::ptr::null(),0,0),
  PE::MissingRequiredSignature=>(7,0,core::ptr::null(),0,0),
  PE::AccountAlreadyInitialized=>(8,0,core::ptr::null(),0,0),
  PE::UninitializedAccount=>(9,0,core::ptr::null(),0,0),
  PE::NotEnoughAccountKeys=>(10,0,core::ptr::null(),0,0),
  PE::AccountBorrowFailed=>(11,0,core::ptr::null(),0,0),
  PE::MaxSeedLengthExceeded=>(12,0,core::ptr::null(),0,0),
  PE::InvalidSeeds=>(13,0,core::ptr::null(),0,0),
  PE::BorshIoError(s)=>(14,0,s.as_ptr(),s.len(),s.capacity()),
  PE::AccountNotRentExempt=>(15,0,core::ptr::null(),0,0),
  PE::UnsupportedSysvar=>(16,0,core::ptr::null(),0,0),
  PE::IllegalOwner=>(17,0,core::ptr::null(),0,0),
  PE::MaxAccountsDataAllocationsExceeded=>(18,0,core::ptr::null(),0,0),
  PE::InvalidRealloc=>(19,0,core::ptr::null(),0,0),
  PE::MaxInstructionTraceLengthExceeded=>(20,0,core::ptr::null(),0,0),
  PE::BuiltinProgramsMustConsumeComputeUnits=>(21,0,core::ptr::null(),0,0),
  PE::InvalidAccountOwner=>(22,0,core::ptr::null(),0,0),
  PE::ArithmeticOverflow=>(23,0,core::ptr::null(),0,0),
  PE::Immutable=>(24,0,core::ptr::null(),0,0),
  PE::IncorrectAuthority=>(25,0,core::ptr::null(),0,0),
 };
 NMN_ErrorSig{tag,custom,ptr,len,cap}
}
fn NMN_any_error()->PE {let tag:u8=kani::any();kani::assume(tag<26);NMN_error_tag(tag)}
fn NMN_error_tag(tag:u8)->PE {
 kani::assume(tag<26);
 match tag {0=>PE::Custom(kani::any()),1=>PE::InvalidArgument,2=>PE::InvalidInstructionData,
 3=>PE::InvalidAccountData,4=>PE::AccountDataTooSmall,5=>PE::InsufficientFunds,6=>PE::IncorrectProgramId,
 7=>PE::MissingRequiredSignature,8=>PE::AccountAlreadyInitialized,9=>PE::UninitializedAccount,
 10=>PE::NotEnoughAccountKeys,11=>PE::AccountBorrowFailed,12=>PE::MaxSeedLengthExceeded,13=>PE::InvalidSeeds,
 14=>{let b:u8=kani::any();kani::assume(b<128);PE::BorshIoError(String::from(char::from(b)))},
 15=>PE::AccountNotRentExempt,16=>PE::UnsupportedSysvar,17=>PE::IllegalOwner,
 18=>PE::MaxAccountsDataAllocationsExceeded,19=>PE::InvalidRealloc,20=>PE::MaxInstructionTraceLengthExceeded,
 21=>PE::BuiltinProgramsMustConsumeComputeUnits,22=>PE::InvalidAccountOwner,23=>PE::ArithmeticOverflow,
 24=>PE::Immutable,_=>PE::IncorrectAuthority}
}
#[derive(Clone,Copy)]
struct NMN_Log241 { entered:bool,program:*const Pubkey,accounts:*const OwnedAccount,count:usize,
 data:*const u8,len:usize,slot:u64,reply:NMN_ErrorSig,omit:bool,statement:*const PoolV1PairForestTerminalStatementV1,focus_i:usize,focus_byte:u8,focus:bool,slot_error:NMN_ErrorSig,slot_is_error:bool }
#[repr(C)]
struct NMN_Key { key:Pubkey,log:UnsafeCell<NMN_Log241> }
fn NMN_validate_error(program:&Pubkey,accounts:&[OwnedAccount],data:&[u8],slot:Result<u64,PE>)->Result<ValidatedAsqa,PE>{
 let p=program as *const Pubkey as *const NMN_Key;
 let error=NMN_any_error();let sig=NMN_sig(&error);
 let slot=match slot{Ok(x)=>x,Err(_)=>panic!("this diagnostic has Ok slot only")};
 unsafe{if !(*(*p).log.get()).omit {*(*p).log.get()=NMN_Log241{entered:true,program,accounts:accounts.as_ptr(),count:accounts.len(),data:data.as_ptr(),len:data.len(),slot,reply:sig,omit:false,statement:core::ptr::null(),focus_i:0,focus_byte:0,focus:false,slot_error:NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0},slot_is_error:false};}}
 Err(error)
}
fn NMN_same(a:NMN_ErrorSig,b:NMN_ErrorSig){
 assert_eq!(a.tag,b.tag);assert_eq!(a.custom,b.custom);assert_eq!(a.ptr,b.ptr);assert_eq!(a.len,b.len);assert_eq!(a.cap,b.cap);
}
fn NMN_241_error<const ARG:bool,const OMIT:bool,const IGNORE:bool>(){
 let zero=NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0};
 let seed=NMN_Log241{entered:false,program:core::ptr::null(),accounts:core::ptr::null(),count:0,data:core::ptr::null(),len:0,slot:0,reply:zero,omit:OMIT,statement:core::ptr::null(),focus_i:0,focus_byte:0,focus:false,slot_error:NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0},slot_is_error:false};
 let key=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 let other=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 // Account buffers are unread on this branch. Empty payloads are an explicit
 // diagnostic restriction, not a full241 domain or native packet.
 let accounts:[OwnedAccount;7]=core::array::from_fn(|_|OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Ok(Vec::new())});
 let mut data:[u8;320]=kani::any();data[0]=b'A';data[1]=b'S';data[2]=b'Q';data[3]=b'8';
 let slot:u64=kani::any();
 let result=stage2_owned(if ARG{&other.key}else{&key.key},&accounts,&data,Ok(slot));
 let log=unsafe{*key.log.get()};assert!(log.entered,"242 call record write");
 assert_eq!(log.program,&key.key as *const Pubkey);assert_eq!(log.accounts,accounts.as_ptr());assert_eq!(log.count,7);
 assert_eq!(log.data,data.as_ptr());assert_eq!(log.len,data.len());assert_eq!(log.slot,slot);
 let error=result.expect_err("242 rejection propagates");
 NMN_same(NMN_sig(&error),if IGNORE{zero}else{log.reply});
 if log.focus{match &error{PE::BorshIoError(text)=>assert_eq!(text.as_bytes()[log.focus_i],log.focus_byte,"returned String byte window"),_=>panic!("String variant lost")}}
}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_validate_error(){NMN_241_error::<false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_validate_reply_control(){NMN_241_error::<false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_validate_argument_control(){NMN_241_error::<true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_validate_write_control(){NMN_241_error::<false,true,false>();}

fn NMN_validate_box(program:&Pubkey,accounts:&[OwnedAccount],data:&[u8],slot:Result<u64,PE>)->Result<ValidatedAsqa,PE>{
 let p=program as *const Pubkey as *const NMN_Key;
 let variant=unsafe{(*(*p).log.get()).reply.tag};
 let value=NMN_statement_variant(variant==1);let layout=Layout::new::<PoolV1PairForestTerminalStatementV1>();
 let raw=unsafe{NMN_ALLOCATOR.alloc(layout)};
 if raw.is_null(){std::alloc::handle_alloc_error(layout);}
 let ptr=raw.cast::<PoolV1PairForestTerminalStatementV1>();unsafe{ptr.write(value);}
 let statement=unsafe{Box::from_raw(ptr)};
 let statement_ptr=&*statement as *const PoolV1PairForestTerminalStatementV1;
 let owner=unsafe{*(*p).log.get()};
 unsafe{NMN_set_owner(statement_ptr.cast(),p.cast_mut().cast());
  if !owner.omit {*(*p).log.get()=NMN_Log241{entered:true,program,accounts:accounts.as_ptr(),count:accounts.len(),data:data.as_ptr(),len:data.len(),slot:slot.unwrap(),reply:owner.reply,omit:false,statement:statement_ptr,focus_i:0,focus_byte:0,focus:false,slot_error:NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0},slot_is_error:false};}}
 Ok(ValidatedAsqa{statement,proof_length:kani::any()})
}
fn NMN_241_box<const VAR:u8,const ARG:bool,const OMIT:bool,const WRONG:bool>(){
 let zero=NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0};
 let seed=NMN_Log241{entered:false,program:core::ptr::null(),accounts:core::ptr::null(),count:0,data:core::ptr::null(),len:0,slot:0,reply:NMN_ErrorSig{tag:VAR,..zero},omit:OMIT,statement:core::ptr::null(),focus_i:0,focus_byte:0,focus:false,slot_error:NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0},slot_is_error:false};
 let key=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 let other=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 let accounts:[OwnedAccount;7]=core::array::from_fn(|_|OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Ok(Vec::new())});
 let mut data:[u8;320]=kani::any();data[0]=b'A';data[1]=b'S';data[2]=b'Q';data[3]=b'8';let slot:u64=kani::any();
 let result=stage2_owned(if ARG{&other.key}else{&key.key},&accounts,&data,Ok(slot));
 let log=unsafe{*key.log.get()};assert!(log.entered);assert_eq!(log.program,&key.key as *const Pubkey);
 assert_eq!(log.accounts,accounts.as_ptr());assert_eq!(log.count,7);assert_eq!(log.data,data.as_ptr());assert_eq!(log.len,320);assert_eq!(log.slot,slot);
 assert_eq!(result,if WRONG{Ok(())}else{Err(PE::InvalidAccountData)});
 assert!(!log.statement.is_null());
 if !log.statement.is_null(){let saved=unsafe{NMN_owner(log.statement.cast())};
 assert_eq!(saved,(&key as *const NMN_Key).cast_mut().cast(),"fresh allocation LOCAL owner survives nonobservable drop");}
}
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_box)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_empty_getter)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_box_constructor(){NMN_241_box::<0,false,false,false>();}
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_box)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_empty_getter)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_box_reply_control(){NMN_241_box::<0,false,false,true>();}
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_box)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_empty_getter)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_box_argument_control(){NMN_241_box::<0,true,false,false>();}
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_box)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_empty_getter)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_box_write_control(){NMN_241_box::<0,false,true,false>();}

fn NMN_validate_error_fixed(program:&Pubkey,accounts:&[OwnedAccount],data:&[u8],slot:Result<u64,PE>)->Result<ValidatedAsqa,PE>{
 let p=program as *const Pubkey as *const NMN_Key;
 let tag=unsafe{(*(*p).log.get()).reply.tag};let error=NMN_error_tag(tag);let sig=NMN_sig(&error);
 let slot=match slot{Ok(x)=>x,Err(_)=>panic!("this diagnostic has Ok slot only")};
 unsafe{if !(*(*p).log.get()).omit {*(*p).log.get()=NMN_Log241{entered:true,program,accounts:accounts.as_ptr(),count:accounts.len(),data:data.as_ptr(),len:data.len(),slot,reply:sig,omit:false,statement:core::ptr::null(),focus_i:0,focus_byte:0,focus:false,slot_error:NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0},slot_is_error:false};}}
 Err(error)
}
fn NMN_241_error_tag<const TAG:u8,const ARG:bool,const OMIT:bool,const IGNORE:bool>(){
 let zero=NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0};
 let seed=NMN_Log241{entered:false,program:core::ptr::null(),accounts:core::ptr::null(),count:0,data:core::ptr::null(),len:0,slot:0,reply:NMN_ErrorSig{tag:TAG,..zero},omit:OMIT,statement:core::ptr::null(),focus_i:0,focus_byte:0,focus:false,slot_error:NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0},slot_is_error:false};
 let key=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 let other=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 // Account buffers are unread on this branch. Empty payloads are an explicit
 // diagnostic restriction, not a full241 domain or native packet.
 let accounts:[OwnedAccount;7]=core::array::from_fn(|_|OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Ok(Vec::new())});
 let mut data:[u8;320]=kani::any();data[0]=b'A';data[1]=b'S';data[2]=b'Q';data[3]=b'8';
 let slot:u64=kani::any();
 let result=stage2_owned(if ARG{&other.key}else{&key.key},&accounts,&data,Ok(slot));
 let log=unsafe{*key.log.get()};assert!(log.entered,"242 call record write");
 assert_eq!(log.program,&key.key as *const Pubkey);assert_eq!(log.accounts,accounts.as_ptr());assert_eq!(log.count,7);
 assert_eq!(log.data,data.as_ptr());assert_eq!(log.len,data.len());assert_eq!(log.slot,slot);
 let error=result.expect_err("242 rejection propagates");
 NMN_same(NMN_sig(&error),if IGNORE{zero}else{log.reply});
 if log.focus{match &error{PE::BorshIoError(text)=>assert_eq!(text.as_bytes()[log.focus_i],log.focus_byte,"returned String byte window"),_=>panic!("String variant lost")}}
}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag0(){NMN_241_error_tag::<0,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag1(){NMN_241_error_tag::<1,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag2(){NMN_241_error_tag::<2,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag3(){NMN_241_error_tag::<3,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag4(){NMN_241_error_tag::<4,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag5(){NMN_241_error_tag::<5,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag6(){NMN_241_error_tag::<6,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag7(){NMN_241_error_tag::<7,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag8(){NMN_241_error_tag::<8,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag9(){NMN_241_error_tag::<9,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag10(){NMN_241_error_tag::<10,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag11(){NMN_241_error_tag::<11,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag12(){NMN_241_error_tag::<12,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag13(){NMN_241_error_tag::<13,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag14(){NMN_241_error_tag::<14,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag15(){NMN_241_error_tag::<15,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag16(){NMN_241_error_tag::<16,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag17(){NMN_241_error_tag::<17,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag18(){NMN_241_error_tag::<18,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag19(){NMN_241_error_tag::<19,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag20(){NMN_241_error_tag::<20,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag21(){NMN_241_error_tag::<21,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag22(){NMN_241_error_tag::<22,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag23(){NMN_241_error_tag::<23,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag24(){NMN_241_error_tag::<24,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_tag25(){NMN_241_error_tag::<25,false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_reply_tag0(){NMN_241_error_tag::<0,false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_argument_tag0(){NMN_241_error_tag::<0,true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_write_tag0(){NMN_241_error_tag::<0,false,true,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_reply_tag1(){NMN_241_error_tag::<1,false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_argument_tag1(){NMN_241_error_tag::<1,true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_write_tag1(){NMN_241_error_tag::<1,false,true,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_reply_tag14(){NMN_241_error_tag::<14,false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_argument_tag14(){NMN_241_error_tag::<14,true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_fixed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_error_write_tag14(){NMN_241_error_tag::<14,false,true,false>();}
// Allocator-channel isolation only, not source/row credit.
unsafe fn NMN_retained_dealloc(_ptr:*mut u8,_layout:Layout){}
fn NMN_direct_allocation<const OMIT:bool,const VALUE:bool>(){
 let a=NMN_Allocator;let layout=Layout::new::<u64>();let p=unsafe{a.alloc(layout)};
 if p.is_null(){return;}
 let mut cell=0u8;let owner=(&mut cell as *mut u8).cast::<()>();
 if !OMIT{unsafe{NMN_set_owner(p,owner);}}
 assert_eq!(unsafe{NMN_owner(p)},owner,"direct allocator LOCAL header");
 let x:u64=kani::any();unsafe{p.cast::<u64>().write(if VALUE{0}else{x});}
 assert_eq!(unsafe{p.cast::<u64>().read()},x,"direct typed payload");
}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_allocator_direct(){NMN_direct_allocation::<false,false>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_allocator_omission(){NMN_direct_allocation::<true,false>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_allocator_value_control(){NMN_direct_allocation::<false,true>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_allocator_box_dispatch(){let b=Box::new(kani::any::<u64>());let p=(&*b as *const u64).cast::<u8>();assert!(unsafe{NMN_owner(p)}.is_null());}
fn NMN_from_raw<const OMIT:bool>(){
 let a=NMN_Allocator;let layout=Layout::new::<u64>();let p=unsafe{a.alloc(layout)};
 if p.is_null(){return;}
 let mut cell=0u8;let owner=(&mut cell as *mut u8).cast::<()>();
 if !OMIT{unsafe{NMN_set_owner(p,owner);}}
 let x:u64=kani::any();unsafe{p.cast::<u64>().write(x);}
 let b=unsafe{Box::from_raw(p.cast::<u64>())};assert_eq!(*b,x);drop(b);
 assert_eq!(unsafe{NMN_owner(p)},owner,"retained fresh header after Box cleanup");
}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_allocator_from_raw(){NMN_from_raw::<false>();}
#[kani::proof]#[kani::unwind(33)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_allocator_from_raw_control(){NMN_from_raw::<true>();}

#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_box)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_empty_getter)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_box_withdrawal(){NMN_241_box::<1,false,false,false>();}

// Defensive cuts for branches that must end before these calls. No SHA/field
// implementation may be accidentally unwound while diagnosing a carrier.
fn NMN_unexpected_encoder(_: &PoolV1PairForestTerminalStatementV1)->Result<[u8;1880],PoolV1PairForestTerminalFormatErrorV1>{panic!("unexpected encoder suffix");}
fn NMN_unexpected_auth<H:aspis_core::Digest32>(_:&[u8],_:&[u8],_:&[u8],_:H,_:verifier::Observer)->Result<(),verifier::Error>{panic!("unexpected auth suffix");}
fn NMN_unexpected_emit(_: &PoolV1PairForestTerminalStatementV1)->ProgramResult{panic!("unexpected emit suffix");}
fn NMN_unexpected_error(_:verifier::Error)->PE{panic!("unexpected error mapping suffix");}
fn NMN_empty_getter(a:&OwnedAccount)->Result<&[u8],PE>{
 match &a.bytes{Ok(v)=>{assert_eq!(v.len(),0,"diagnostic input-array buffer constructor fidelity");Ok(&[])},Err(_)=>panic!("diagnostic input array changed stored Result")}
}
fn NMN_validate_error_nostring(program:&Pubkey,accounts:&[OwnedAccount],data:&[u8],slot:Result<u64,PE>)->Result<ValidatedAsqa,PE>{
 let p=program as *const Pubkey as *const NMN_Key;
 let tag:u8=kani::any();kani::assume(tag<26 && tag!=14);let error=NMN_error_tag(tag);let sig=NMN_sig(&error);
 let (slot,slot_error,slot_is_error)=match slot{Ok(v)=>(v,NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0},false),Err(e)=>(0,NMN_sig(&e),true)};unsafe{if !(*(*p).log.get()).omit{*(*p).log.get()=NMN_Log241{entered:true,program,accounts:accounts.as_ptr(),count:accounts.len(),data:data.as_ptr(),len:data.len(),slot,reply:sig,omit:false,statement:core::ptr::null(),focus_i:0,focus_byte:0,focus:false,slot_error,slot_is_error};}}
 Err(error)
}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_nonstrings(){NMN_241_error::<false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_nonstrings_reply(){NMN_241_error::<false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_nonstrings_argument(){NMN_241_error::<true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]
#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_nonstrings_write(){NMN_241_error::<false,true,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_box)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_empty_getter)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_box_withdrawal_reply(){NMN_241_box::<1,false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_box)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_empty_getter)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_box_withdrawal_argument(){NMN_241_box::<1,true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_box)]
#[kani::stub(crate::r1_pool_adapter::owned::OwnedAccount::data,NMN_empty_getter)]
#[kani::stub(std::alloc::dealloc,NMN_retained_dealloc)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_box_withdrawal_write(){NMN_241_box::<1,false,true,false>();}

fn NMN_validate_string(program:&Pubkey,accounts:&[OwnedAccount],data:&[u8],slot:Result<u64,PE>)->Result<ValidatedAsqa,PE>{
 let p=program as *const Pubkey as *const NMN_Key;
 let bytes:[u8;16]=kani::any();for byte in &bytes{kani::assume(*byte<128);}
 let n:usize=kani::any();kani::assume(n<=16);
 // Every selected byte is ASCII, so this constructs a valid String.
 let text=unsafe{String::from_utf8_unchecked(bytes[..n].to_vec())};
 let error=PE::BorshIoError(text);let sig=NMN_sig(&error);
 let mut log=unsafe{*(*p).log.get()};
 if !log.omit{
  log.entered=true;log.program=program;log.accounts=accounts.as_ptr();log.count=accounts.len();log.data=data.as_ptr();log.len=data.len();log.slot=slot.unwrap();log.reply=sig;
  if n>0{let i:usize=kani::any();kani::assume(i<n);log.focus=true;log.focus_i=i;log.focus_byte=bytes[i];}
  unsafe{*(*p).log.get()=log;}
 }
 Err(error)
}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_string)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_string_window(){NMN_241_error::<false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_string)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_string_reply(){NMN_241_error::<false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_string)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_string_argument(){NMN_241_error::<true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_string)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_string_write(){NMN_241_error::<false,true,false>();}

fn NMN_241_sloterror<const ARG:bool,const OMIT:bool,const IGNORE:bool>(){
 let zero=NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0};
 let seed=NMN_Log241{entered:false,program:core::ptr::null(),accounts:core::ptr::null(),count:0,data:core::ptr::null(),len:0,slot:0,reply:zero,omit:OMIT,statement:core::ptr::null(),focus_i:0,focus_byte:0,focus:false,slot_error:NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0},slot_is_error:false};
 let key=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 let other=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 // Account buffers are unread on this branch. Empty payloads are an explicit
 // diagnostic restriction, not a full241 domain or native packet.
 let accounts:[OwnedAccount;7]=core::array::from_fn(|_|OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Ok(Vec::new())});
 let mut data:[u8;320]=kani::any();data[0]=b'A';data[1]=b'S';data[2]=b'Q';data[3]=b'8';
 let t:u8=kani::any();kani::assume(t<26 && t!=14);let input=NMN_error_tag(t);let before_slot=NMN_sig(&input);
 let result=stage2_owned(if ARG{&other.key}else{&key.key},&accounts,&data,Err(input));
 let log=unsafe{*key.log.get()};assert!(log.entered,"242 call record write");
 assert_eq!(log.program,&key.key as *const Pubkey);assert_eq!(log.accounts,accounts.as_ptr());assert_eq!(log.count,7);
 assert_eq!(log.data,data.as_ptr());assert_eq!(log.len,data.len());assert!(log.slot_is_error);NMN_same(log.slot_error,before_slot);
 let error=result.expect_err("242 rejection propagates");
 NMN_same(NMN_sig(&error),if IGNORE{zero}else{log.reply});
 if log.focus{match &error{PE::BorshIoError(text)=>assert_eq!(text.as_bytes()[log.focus_i],log.focus_byte,"returned String byte window"),_=>panic!("String variant lost")}}
}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_slot_error(){NMN_241_sloterror::<false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_slot_reply(){NMN_241_sloterror::<false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_slot_argument(){NMN_241_sloterror::<true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_slot_write(){NMN_241_sloterror::<false,true,false>();}

include!("NMN_full.rs");

// Unicode scalar payload partition, not an unbounded String certificate.
fn NMN_validate_unicode(program:&Pubkey,accounts:&[OwnedAccount],data:&[u8],slot:Result<u64,PE>)->Result<ValidatedAsqa,PE>{
 let p=program as *const Pubkey as *const NMN_Key;
 let u:u32=kani::any();kani::assume(u<=0x10ffff && !(0xd800..=0xdfff).contains(&u));
 let c=char::from_u32(u).unwrap();let mut bytes=[0u8;4];let n=c.encode_utf8(&mut bytes).len();
 let text=unsafe{String::from_utf8_unchecked(bytes[..n].to_vec())};
 let error=PE::BorshIoError(text);let sig=NMN_sig(&error);
 let mut log=unsafe{*(*p).log.get()};
 if !log.omit{
  log.entered=true;log.program=program;log.accounts=accounts.as_ptr();log.count=accounts.len();log.data=data.as_ptr();log.len=data.len();log.slot=slot.unwrap();log.reply=sig;
  if n>0{let i:usize=kani::any();kani::assume(i<n);log.focus=true;log.focus_i=i;log.focus_byte=bytes[i];}
  unsafe{*(*p).log.get()=log;}
 }
 Err(error)
}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_unicode)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_unicode_window(){NMN_241_error::<false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_unicode)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_unicode_reply(){NMN_241_error::<false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_unicode)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_unicode_argument(){NMN_241_error::<true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_unicode)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_unicode_write(){NMN_241_error::<false,true,false>();}


fn NMN_241_unicodeslot<const ARG:bool,const OMIT:bool,const IGNORE:bool>(){
 let zero=NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0};
 let seed=NMN_Log241{entered:false,program:core::ptr::null(),accounts:core::ptr::null(),count:0,data:core::ptr::null(),len:0,slot:0,reply:zero,omit:OMIT,statement:core::ptr::null(),focus_i:0,focus_byte:0,focus:false,slot_error:NMN_ErrorSig{tag:0,custom:0,ptr:core::ptr::null(),len:0,cap:0},slot_is_error:false};
 let key=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 let other=NMN_Key{key:Pubkey::new_from_array(kani::any()),log:UnsafeCell::new(seed)};
 // Account buffers are unread on this branch. Empty payloads are an explicit
 // diagnostic restriction, not a full241 domain or native packet.
 let accounts:[OwnedAccount;7]=core::array::from_fn(|_|OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Ok(Vec::new())});
 let mut data:[u8;320]=kani::any();data[0]=b'A';data[1]=b'S';data[2]=b'Q';data[3]=b'8';
 let u:u32=kani::any();kani::assume(u<=0x10ffff && !(0xd800..=0xdfff).contains(&u));let c=char::from_u32(u).unwrap();let mut bytes=[0u8;4];let text=c.encode_utf8(&mut bytes);let input=PE::BorshIoError(text.to_owned());let before_slot=NMN_sig(&input);
 let result=stage2_owned(if ARG{&other.key}else{&key.key},&accounts,&data,Err(input));
 let log=unsafe{*key.log.get()};assert!(log.entered,"242 call record write");
 assert_eq!(log.program,&key.key as *const Pubkey);assert_eq!(log.accounts,accounts.as_ptr());assert_eq!(log.count,7);
 assert_eq!(log.data,data.as_ptr());assert_eq!(log.len,data.len());assert!(log.slot_is_error);NMN_same(log.slot_error,before_slot);
 let error=result.expect_err("242 rejection propagates");
 NMN_same(NMN_sig(&error),if IGNORE{zero}else{log.reply});
 if log.focus{match &error{PE::BorshIoError(text)=>assert_eq!(text.as_bytes()[log.focus_i],log.focus_byte,"returned String byte window"),_=>panic!("String variant lost")}}
}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_unicode_slot_error(){NMN_241_unicodeslot::<false,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_unicode_slot_reply(){NMN_241_unicodeslot::<false,false,true>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_unicode_slot_argument(){NMN_241_unicodeslot::<true,false,false>();}
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1,NMN_unexpected_encoder)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx2_authenticated::<crate::SolanaDigest>,NMN_unexpected_auth)]
#[kani::stub(emit_result,NMN_unexpected_emit)]#[kani::stub(crate::error,NMN_unexpected_error)]
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_validate_error_nostring)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_241_unicode_slot_write(){NMN_241_unicodeslot::<false,true,false>();}

fn NMN_prefix_stop(_: &Pubkey,_:&[OwnedAccount],_:&[u8],_:Result<u64,PE>)->Result<ValidatedAsqa,PE>{panic!("242 must not be entered before guard");}
fn NMN_guard<const MODE:u8,const BAD:bool>(){
 let key=Pubkey::new_from_array(kani::any());
 let accounts:[OwnedAccount;9]=core::array::from_fn(|_|OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Ok(Vec::new())});
 let mut data:[u8;320]=kani::any();let n:usize=kani::any();let count:usize;let length:usize;
 if MODE==0{kani::assume(n<=9 && n!=7);count=n;length=320;}
 else if MODE==1{kani::assume(n<4);count=7;length=n;}
 else{kani::assume(n<4);count=7;length=320;data[0]=b'A';data[1]=b'S';data[2]=b'Q';data[3]=b'8';let x:u8=kani::any();kani::assume(x!=data[n]);data[n]=x;}
 let result=stage2_owned(&key,&accounts[..count],&data[..length],Ok(kani::any()));
 assert_eq!(result,Err(if BAD{PE::InvalidAccountData}else{PE::InvalidInstructionData}),"native prefix guard result");
}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_prefix_stop)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_guard_count_pass(){NMN_guard::<0,false>();}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_prefix_stop)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_guard_count_control(){NMN_guard::<0,true>();}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_prefix_stop)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_guard_short_pass(){NMN_guard::<1,false>();}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_prefix_stop)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_guard_short_control(){NMN_guard::<1,true>();}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_prefix_stop)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_guard_magic_pass(){NMN_guard::<2,false>();}
#[kani::proof]#[kani::unwind(33)]#[kani::stub(validate_asq8,NMN_prefix_stop)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMN_guard_magic_control(){NMN_guard::<2,true>();}
