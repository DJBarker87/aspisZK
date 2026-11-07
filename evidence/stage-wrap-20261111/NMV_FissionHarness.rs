use super::NMV_Fission::*;
use super::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
#[derive(Clone,Copy,Default)]
struct Event { tag:u8, account:u64, l1:usize, l2:usize }
struct Log<const MODE:u8> {
 events:[Event;12], n:usize, replies:[u64;7], sn:usize,
 seen:[u64;7], count:usize, pid:u8, coord:usize,
 data0:u8, data_ptr:usize, data_len:usize, copy_ptr:usize, slot_seen:Result<u64,u32>, slot:Result<u64,u32>,
 reply:Option<ProgramResult>, cp:Option<Result<Vec<u8>,ProgramError>>,
 borrow_ok:bool, copy_len:usize, copy_byte:u8, copies:usize,
}
impl<const M:u8> Log<M> {
 fn event(&mut self,e:Event){self.events[self.n]=e;self.n+=1;}
 fn args(&mut self,p:&Pubkey,a:&[u64],d:&[u8]) {
  self.pid=p[self.coord];self.count=a.len();self.data0=d[0];self.data_ptr=(d.as_ptr() as usize).wrapping_add(if M==5 {1}else{0});self.data_len=d.len();
  let mut i=0;while i<a.len(){self.seen[i]=if M==2 && i==0 {a[i]^1}else{a[i]};i+=1;}
 }
}
struct Write;
impl<const M:u8> WriteWindow<Log<M>> for Write {
 fn copy_from_slice(self,l:&mut Log<M>,s:&[u8]) {
  l.event(Event{tag:6,..Event::default()});l.copy_len=s.len();l.copy_ptr=s.as_ptr() as usize;
  if !s.is_empty(){l.copy_byte=s[0];}if M!=3 {l.copies+=1;}
 }
}
fn clock_error(e:u32)->ProgramError {ProgramError::Custom(e)}
impl<const M:u8> Windows for Log<M> {
 type Account=u64;type Owned=u64;type Write=Write;
 fn snapshot(l:&mut Self,a:&u64,x:usize,y:usize)->u64 {
  l.event(Event{tag:1,account:*a,l1:x,l2:y});let r=l.replies[l.sn];l.sn+=1;r
 }
 fn stage1_owned(l:&mut Self,p:&Pubkey,a:&[u64],d:&[u8])->Result<Vec<u8>,ProgramError>{
  l.event(Event{tag:4,..Event::default()});l.args(p,a,d);l.cp.take().unwrap()
 }
 fn stage2_owned(l:&mut Self,p:&Pubkey,a:&[u64],d:&[u8],s:Result<u64,ProgramError>)->ProgramResult {
  l.event(Event{tag:4,..Event::default()});l.args(p,a,d);
  l.slot_seen=match s {Ok(s)=>Ok(s),Err(ProgramError::Custom(e))=>Err(e),Err(_)=>panic!()};
  l.reply.take().unwrap()
 }
 fn try_borrow_mut_data(l:&mut Self,a:&u64)->Result<Write,ProgramError> {
  l.event(Event{tag:5,account:*a,..Event::default()});
  if l.borrow_ok {Ok(Write)}else{Err(ProgramError::AccountBorrowFailed)}
 }
 fn set_return_data(l:&mut Self,d:&[u8]){assert!(d.is_empty());if M!=3{l.event(Event{tag:2,..Event::default()});}}
 fn clock_get(l:&mut Self)->Result<Clock,ProgramError>{
  l.event(Event{tag:3,..Event::default()});match l.slot {Ok(s)=>Ok(Clock{slot:s}),Err(e)=>Err(clock_error(e))}
 }
}
fn log<const M:u8>(slot:Result<u64,u32>)->Log<M>{
 Log{events:[Event::default();12],n:0,replies:kani::any(),sn:0,seen:[0;7],count:0,pid:0,coord:0,data0:0,data_ptr:0,data_len:0,copy_ptr:0,slot_seen:Ok(0),slot,
 reply:None,cp:None,borrow_ok:kani::any(),copy_len:0,copy_byte:0,copies:0}
}
// Full declared ProgramError type is used at every boundary; payloads are small
// symbolic carriers, never constraints on a production caller's input.
fn error(k:u8,x:u32,b:u8)->ProgramError {
 match k {
 0=>ProgramError::Custom(x),1=>ProgramError::InvalidArgument,2=>ProgramError::InvalidInstructionData,
 3=>ProgramError::InvalidAccountData,4=>ProgramError::AccountDataTooSmall,5=>ProgramError::InsufficientFunds,
 6=>ProgramError::IncorrectProgramId,7=>ProgramError::MissingRequiredSignature,8=>ProgramError::AccountAlreadyInitialized,
 9=>ProgramError::UninitializedAccount,10=>ProgramError::NotEnoughAccountKeys,11=>ProgramError::AccountBorrowFailed,
 12=>ProgramError::MaxSeedLengthExceeded,13=>ProgramError::InvalidSeeds,
 14=>ProgramError::BorshIoError(char::from(b).to_string()),15=>ProgramError::AccountNotRentExempt,
 16=>ProgramError::UnsupportedSysvar,17=>ProgramError::IllegalOwner,18=>ProgramError::MaxAccountsDataAllocationsExceeded,
 19=>ProgramError::InvalidRealloc,20=>ProgramError::MaxInstructionTraceLengthExceeded,
 21=>ProgramError::BuiltinProgramsMustConsumeComputeUnits,22=>ProgramError::InvalidAccountOwner,
 23=>ProgramError::ArithmeticOverflow,24=>ProgramError::Immutable,_=>ProgramError::IncorrectAuthority}
}
fn same_error(e:ProgramError,k:u8,x:u32,b:u8){
 match (e,k) {
 (ProgramError::Custom(y),0)=>assert_eq!(x,y),
 (ProgramError::InvalidArgument,1)|(ProgramError::InvalidInstructionData,2)|
 (ProgramError::InvalidAccountData,3)|(ProgramError::AccountDataTooSmall,4)|
 (ProgramError::InsufficientFunds,5)|(ProgramError::IncorrectProgramId,6)|
 (ProgramError::MissingRequiredSignature,7)|(ProgramError::AccountAlreadyInitialized,8)|
 (ProgramError::UninitializedAccount,9)|(ProgramError::NotEnoughAccountKeys,10)|
 (ProgramError::AccountBorrowFailed,11)|(ProgramError::MaxSeedLengthExceeded,12)|
 (ProgramError::InvalidSeeds,13)|(ProgramError::AccountNotRentExempt,15)|
 (ProgramError::UnsupportedSysvar,16)|(ProgramError::IllegalOwner,17)|
 (ProgramError::MaxAccountsDataAllocationsExceeded,18)|(ProgramError::InvalidRealloc,19)|
 (ProgramError::MaxInstructionTraceLengthExceeded,20)|(ProgramError::BuiltinProgramsMustConsumeComputeUnits,21)|
 (ProgramError::InvalidAccountOwner,22)|(ProgramError::ArithmeticOverflow,23)|
 (ProgramError::Immutable,24)|(ProgramError::IncorrectAuthority,25)=>{},
 (ProgramError::BorshIoError(s),14)=>{let s=s.as_bytes();if b<128 {assert_eq!(s.len(),1);assert_eq!(s[0],b);}else{assert_eq!(s.len(),2);assert_eq!(s[0],0xc0|(b>>6));assert_eq!(s[1],0x80|(b&63));}},
 _=>panic!("reply changed")}
}
fn stage2_test<const M:u8>() {
 let a:[u64;7]=kani::any();let p:Pubkey=kani::any();let mut d=[65,83,81,56,0];d[4]=kani::any();
 let slot=if kani::any(){Ok(kani::any())}else{Err(kani::any())};let mut l=log::<M>(slot);
 let coord:usize=kani::any();kani::assume(coord<32);l.coord=coord;
 let ok:bool=kani::any();let k:u8=kani::any();kani::assume(k<26);let x:u32=kani::any();let b:u8=kani::any();
 l.reply=Some(if ok{Ok(())}else{Err(error(k,x,b))});
 let out=stage2(&mut l,&p,&a,&d);
 if M==1 {assert!(out.is_ok());}else if ok {assert!(out.is_ok());}else{same_error(out.unwrap_err(),k,x,b);}
 assert_eq!(l.n,10);assert_eq!(l.events[0].tag,2);assert_eq!(l.events[8].tag,3);assert_eq!(l.events[9].tag,4);
 let lens=[(58295,58295),(384,384),(192,192),(768,768),(128,256),(192,320),(1768,1768)];
 let mut i=0;while i<7 {let e=l.events[i+1];assert_eq!(e.tag,1);assert_eq!(e.account,a[i]);assert_eq!((e.l1,e.l2),lens[i]);assert_eq!(l.seen[i],l.replies[i]);i+=1;}
 assert_eq!(l.pid,p[coord]);assert_eq!(l.count,7);assert_eq!(l.data0,65);assert_eq!(l.slot_seen,slot);assert_eq!(l.copies,0);
}
fn stage1_test<const M:u8,const PATH:u8>() {
 let a:[u64;3]=kani::any();let p:Pubkey=kani::any();let d=if kani::any(){[3,10]}else{[3,11]};let mut l=log::<M>(Ok(0));
 let coord:usize=kani::any();kani::assume(coord<32);l.coord=coord;
 let k:u8=kani::any();kani::assume(k<26);let x:u32=kani::any();let b:u8=kani::any();let cp:u8=kani::any();
 l.borrow_ok=PATH!=1;l.cp=Some(if PATH==0{Err(error(k,x,b))}else{Ok(vec![cp])});
 let out=stage1(&mut l,&p,&a,&d);
 if M==1 {assert!(out.is_ok());}else if PATH==0 {same_error(out.unwrap_err(),k,x,b);}else if PATH==1 {assert!(matches!(out,Err(ProgramError::AccountBorrowFailed)));}else{assert!(out.is_ok());}
 assert_eq!(l.n,if PATH==0{4}else if PATH==1{5}else{6});
 let lens=[58295,1880,1768];let mut i=0;while i<3 {let e=l.events[i];assert_eq!(e.tag,1);assert_eq!(e.account,a[i]);assert_eq!(e.l1,lens[i]);assert_eq!(e.l2,lens[i]);assert_eq!(l.seen[i],l.replies[i]);i+=1;}
 assert_eq!(l.events[3].tag,4);assert_eq!(l.pid,p[coord]);assert_eq!(l.count,3);assert_eq!(l.data0,3);
 if PATH!=0{assert_eq!(l.events[4].tag,5);assert_eq!(l.events[4].account,a[2]);}
 if PATH==2{assert_eq!(l.events[5].tag,6);assert_eq!(l.copy_len,1);assert_eq!(l.copy_byte,cp);assert_eq!(l.copies,1);}else{assert_eq!(l.copies,0);}
}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage2_pass(){stage2_test::<0>();}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage2_reply_control(){stage2_test::<1>();}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage2_argument_control(){stage2_test::<2>();}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage2_footprint_control(){stage2_test::<3>();}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage1_child_error(){stage1_test::<0,0>();}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage1_borrow_error(){stage1_test::<0,1>();}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage1_copy(){stage1_test::<0,2>();}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage1_reply_control(){stage1_test::<1,0>();}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage1_argument_control(){stage1_test::<2,2>();}

#[kani::proof]
#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_stage1_footprint_control(){stage1_test::<3,2>();}
// Independent slice-descriptor cuts. The full-result family K035-K044 remains
// unchanged in purpose; no two-enum product is reached in these cuts.
fn slices_stage2<const M:u8>(){
 let a:[u64;7]=kani::any();let p:Pubkey=kani::any();
 let d=[65,83,81,56,kani::any(),kani::any(),kani::any(),kani::any()];
 let n:usize=kani::any();kani::assume(n>=4&&n<=8);let d=&d[..n];
 let mut l=log::<M>(Ok(kani::any()));l.reply=Some(Ok(()));
 let out=stage2(&mut l,&p,&a,d);
 if M==1{assert!(out.is_err());}else{assert!(out.is_ok());}
 assert_eq!(l.data_ptr,d.as_ptr() as usize);assert_eq!(l.data_len,n);
 assert_eq!(l.n,10);assert_eq!(l.count,7);
}
fn slices_stage1<const M:u8>(){
 let a:[u64;3]=kani::any();let p:Pubkey=kani::any();let d=if kani::any(){[3,10]}else{[3,11]};
 let mut l=log::<M>(Ok(0));l.borrow_ok=true;l.cp=Some(Ok(vec![kani::any()]));
 let out=stage1(&mut l,&p,&a,&d);
 if M==1{assert!(out.is_err());}else{assert!(out.is_ok());}
 assert_eq!(l.data_ptr,d.as_ptr() as usize);assert_eq!(l.data_len,2);assert_eq!(l.copies,1);
}
struct CLog<const M:u8>{ base:Log<0>, reply:Option<Result<Clock,ProgramError>>, seen:Option<Result<u64,ProgramError>> }
struct CWrite;
impl<const M:u8> WriteWindow<CLog<M>> for CWrite {fn copy_from_slice(self,_:&mut CLog<M>,_:&[u8]){panic!()}}
impl<const M:u8> Windows for CLog<M>{
 type Account=u64;type Owned=u64;type Write=CWrite;
 fn snapshot(l:&mut Self,a:&u64,x:usize,y:usize)->u64{<Log<0> as Windows>::snapshot(&mut l.base,a,x,y)}
 fn stage1_owned(_:&mut Self,_:&Pubkey,_:&[u64],_:&[u8])->Result<Vec<u8>,ProgramError>{panic!()}
 fn stage2_owned(l:&mut Self,p:&Pubkey,a:&[u64],d:&[u8],s:Result<u64,ProgramError>)->ProgramResult{l.base.args(p,a,d);l.seen=Some(s);Ok(())}
 fn try_borrow_mut_data(_:&mut Self,_:&u64)->Result<CWrite,ProgramError>{panic!()}
 fn set_return_data(l:&mut Self,d:&[u8]){<Log<0> as Windows>::set_return_data(&mut l.base,d)}
 fn clock_get(l:&mut Self)->Result<Clock,ProgramError>{if M==1{Ok(Clock{slot:0})}else{l.reply.take().unwrap()}}
}
fn clock_test<const M:u8>(){
 let k:u8=kani::any();kani::assume(k<26);let x:u32=kani::any();let b:u8=kani::any();let slot:u64=kani::any();let ok:bool=kani::any();
 let mut l=CLog::<M>{base:log::<0>(Ok(0)),reply:Some(if ok{Ok(Clock{slot})}else{Err(error(k,x,b))}),seen:None};
 let a:[u64;7]=kani::any();let p:Pubkey=kani::any();
 assert!(stage2(&mut l,&p,&a,&[65,83,81,56]).is_ok());
 let s=l.seen.unwrap();if ok {match s{Ok(v)=>assert_eq!(v,slot),Err(_)=>panic!()}}else{same_error(s.unwrap_err(),k,x,b);}
 assert_eq!(l.base.data_len,4);assert_eq!(l.base.sn,7);
}
fn copy_descriptor_test(){
 let a:[u64;3]=kani::any();let p:Pubkey=kani::any();let d=[3,10];let n:usize=kani::any();kani::assume(n<=4);
 let mut cp=Vec::with_capacity(4);let mut i=0;while i<n{cp.push(kani::any());i+=1;}
 let ptr=cp.as_ptr() as usize;
 let mut l=log::<0>(Ok(0));l.borrow_ok=true;l.cp=Some(Ok(cp));
 assert!(stage1(&mut l,&p,&a,&d).is_ok());
 assert_eq!(l.copy_ptr,ptr);assert_eq!(l.copy_len,n);assert_eq!(l.copies,1);
}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_slice2_pass(){slices_stage2::<0>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_slice2_reply_control(){slices_stage2::<1>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_slice2_argument_control(){slices_stage2::<5>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_slice2_footprint_control(){slices_stage2::<3>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_slice1_pass(){slices_stage1::<0>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_slice1_reply_control(){slices_stage1::<1>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_slice1_argument_control(){slices_stage1::<5>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_slice1_footprint_control(){slices_stage1::<3>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_clock_pass(){clock_test::<0>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_clock_reply_control(){clock_test::<1>();}

#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_copy_descriptor(){copy_descriptor_test();}
#[kani::proof]#[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_fission_rejected_routes(){
 let a:[u64;7]=kani::any();let n:usize=kani::any();kani::assume(n<=7);
 let d:[u8;5]=kani::any();let m:usize=kani::any();kani::assume(m<=5);
 let data=&d[..m];let accounts=&a[..n];let p:Pubkey=kani::any();
 kani::assume(!(data==&[3,10]||data==&[3,11])||n!=3);
 kani::assume(n!=7||data.get(..4)!=Some(&[65,83,81,56][..]));
 let mut l1=log::<0>(Ok(0));let mut l2=log::<0>(Ok(0));
 assert!(matches!(stage1(&mut l1,&p,accounts,data),Err(ProgramError::InvalidInstructionData)));
 assert!(matches!(stage2(&mut l2,&p,accounts,data),Err(ProgramError::InvalidInstructionData)));
 assert_eq!(l1.n,0);assert_eq!(l2.n,0);
}
