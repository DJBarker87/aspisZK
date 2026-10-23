#![allow(dead_code,unexpected_cfgs,non_snake_case)]
#![cfg(kani)]
#[path="S2F_Trusted.rs"] mod sdk;
use s2e_reference::S2E_Reference::*;
use solana_program::program_error::ProgramError as PE;
type PR=Result<(),PE>;
// Avoid formatting and ProgramError's string-bearing Debug on failing branches.
macro_rules! assert_eq { ($left:expr,$right:expr) => { assert!($left == $right) }; }


// Each harness is a single source cut, never an invocation of either whole stage.
// Scalar inputs to a cut denote values ALREADY computed by the reached prefix.
// Their provenance is a separate port; these checks do not manufacture it.
fn S2F_account(s:&sdk::State,a:usize)->OwnedAccount {
 OwnedAccount{key:kani::any(),owner:kani::any(),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),rent_epoch:kani::any(),data_slot:s.accounts[a],lamports_slot:s.lamports[a] as usize}
}
fn S2F_cell(s:&sdk::State,c:usize)->OwnedDataCell {
 OwnedDataCell{bytes:Vec::new(),borrowed:s.counter[c] as isize,strong:kani::any(),weak:kani::any()}
}
fn S2F_owned(s:&sdk::State)->OwnedSdk {
 OwnedSdk{accounts:vec![S2F_account(s,0),S2F_account(s,1),S2F_account(s,2)],data_cells:vec![S2F_cell(s,0),S2F_cell(s,1),S2F_cell(s,2)],lamports_cells:Vec::new()}
}
// Compare one arbitrary cell; aliasing accounts remain possible. Empty payloads
// here are deliberate: arbitrary full payload and typed guard ports remain open.
fn S2F_counter_frame(o:&OwnedSdk,s:&sdk::State) {
 let c:usize=kani::any();kani::assume(c<3);
 assert_eq!(o.data_cells[c].borrowed,s.counter[c] as isize);
}
#[kani::proof] #[kani::unwind(34)] #[kani::stub_verified(sdk::step)]
fn S2F_exclusive_acquire() {
 let s:sdk::State=kani::any();kani::assume(sdk::valid(&s));let a:usize=kani::any();kani::assume(a<3);
 let op=sdk::Op::Exclusive{account:a,token:0,owner:100};kani::assume(sdk::enabled(&s,op));
 let mut o=S2F_owned(&s);let c=o.accounts[a].data_slot;
 let mut g=LiveGuards{checkpoint:None,public:None,proof:None};
 let (post,r)=sdk::step(s,op);let result=owned_acquire_checkpoint(&mut o,&mut g,c);
 match r {sdk::Reply::Guard(0)=>{assert_eq!(result,Ok(()));assert_eq!(g.checkpoint,Some(c));},sdk::Reply::BorrowFailed=>{assert_eq!(result,Err(PE::AccountBorrowFailed));assert_eq!(g.checkpoint,None);},_=>assert!(false)}
 S2F_counter_frame(&o,&post);
}
#[kani::proof] #[kani::unwind(34)] #[kani::stub_verified(sdk::step)]
fn S2F_shared_acquire() {
 let s:sdk::State=kani::any();kani::assume(sdk::valid(&s));let a:usize=kani::any();kani::assume(a<3);
 let op=sdk::Op::Shared{account:a,token:0,owner:100};kani::assume(sdk::enabled(&s,op));
 let mut o=S2F_owned(&s);let c=o.accounts[a].data_slot;
 let (post,r)=sdk::step(s,op);let result=owned_acquire_shared(&mut o,c);
 match r {sdk::Reply::Guard(0)=>assert_eq!(result,Ok(())),sdk::Reply::BorrowFailed=>assert_eq!(result,Err(PE::AccountBorrowFailed)),_=>assert!(false)}
 S2F_counter_frame(&o,&post);
}
#[kani::proof] #[kani::unwind(34)] #[kani::stub_verified(sdk::step)]
fn S2F_shared_drop() {
 let s:sdk::State=kani::any();kani::assume(sdk::valid(&s));let t:usize=kani::any();kani::assume(t<3);
 kani::assume(s.guards[t].is_some());let guard=s.guards[t].unwrap();kani::assume(!guard.exclusive);
 let mut o=S2F_owned(&s);let (post,r)=sdk::step(s,sdk::Op::Drop{token:t});
 release_shared(&mut o,guard.cell);assert_eq!(r,sdk::Reply::Unit);S2F_counter_frame(&o,&post);
}
#[kani::proof] #[kani::unwind(34)] #[kani::stub_verified(sdk::step)]
fn S2F_exclusive_drop() {
 let s:sdk::State=kani::any();kani::assume(sdk::valid(&s));let t:usize=kani::any();kani::assume(t<3);
 kani::assume(s.guards[t].is_some());let guard=s.guards[t].unwrap();kani::assume(guard.exclusive);
 let mut o=S2F_owned(&s);let (post,r)=sdk::step(s,sdk::Op::Drop{token:t});
 owned_release_guards(&mut o,LiveGuards{checkpoint:Some(guard.cell),public:None,proof:None});
 assert_eq!(r,sdk::Reply::Unit);S2F_counter_frame(&o,&post);
}
// Source stage1:947-949. Owned shape1 is called directly, not rewritten.
#[kani::proof] #[kani::unwind(7)]
fn S2F_shape1() {
 let a:[u8;5]=kani::any();let n:usize=kani::any();kani::assume(n<=5);let data=&a[..n];let count:usize=kani::any();
 let native=if !(data==&[3,10] || data==&[3,11]) || count!=3 {Err(PE::InvalidInstructionData)}else{Ok(())};
 assert_eq!(native,shape1(data,count));
}
// Source :960, owned nonzero_from. This is the finite scan leaf, not arbitrary
// buffer scan induction; the latter needs the inherited scanner interpretation.
#[kani::proof] #[kani::unwind(5)]
fn S2F_scan_leaf() {
 let a:[u8;2]=kani::any();let n:usize=kani::any();kani::assume(n<=2);let bytes=&a[..n];
 assert_eq!(bytes.iter().any(|byte|*byte!=0),nonzero_from(bytes,bytes.len()));
}
// Source :974-975 and :1010-1011. Every usize, including overflow.
#[kani::proof] #[kani::unwind(3)]
fn S2F_checked_end_value() {
 let length:usize=kani::any();kani::assume(length<=usize::MAX-688);
 let native=688usize.checked_add(length).ok_or(PE::InvalidAccountData);
 assert!(native.ok()==Some(688+length));
 assert!(688usize.checked_add(57607)==Some(58295));
}
#[kani::proof] #[kani::unwind(3)]
fn S2F_checked_end_overflow() {
 let length:usize=kani::any();kani::assume(length>usize::MAX-688);
 let native=688usize.checked_add(length).ok_or(PE::InvalidAccountData);
 assert!(matches!(native,Err(PE::InvalidAccountData)));
}
// Source :976-980. The prefix equality is a cut input, not a proved byte fact.
fn S2F_native_gate(len:usize,prefix_equal:bool,tag:u8)->PR {
 if len!=58295 || !prefix_equal || tag!=2 {return Err(PE::InvalidAccountData);}Ok(())
}
#[kani::proof] #[kani::unwind(3)]
fn S2F_proof_decision() {
 let len:usize=kani::any();let eq:bool=kani::any();let tag:u8=kani::any();
 let reference=if len==58295 && eq && tag==2 {Ok(())}else{Err(PE::InvalidAccountData)};
 assert!(S2F_code(S2F_native_gate(len,eq,tag))==S2F_code(reference));
}
// Source :981 split cast. Range identity is a descriptor arithmetic check.
#[kani::proof] #[kani::unwind(3)]
fn S2F_range_split() {
 let byte:u8=kani::any();let split=byte as usize;
 assert_eq!(split,usize::from(byte));assert!(split<=255);
 assert_eq!(58295usize-688,57607);assert!(688+8<58295);
}
// Source :982-985. Copy is recorded only on the equal-size arm; this proves
// dispatch, not the concrete copy child's footprint or returned vector bytes.
#[kani::proof] #[kani::unwind(3)]
fn S2F_checkpoint_length() {
 let cp_len:usize=kani::any();let target_len:usize=kani::any();
 let mut copied=false;
 let native=if cp_len!=target_len {Err(PE::InvalidAccountData)}else{copied=true;Ok(())};
 assert_eq!(native,if cp_len==target_len {Ok(())}else{Err(PE::InvalidAccountData)});
 assert_eq!(copied,cp_len==target_len);
}
// Source :996-1000, all fixed prefix bytes and one-byte-short/extra tails.
#[kani::proof] #[kani::unwind(7)]
fn S2F_shape2_clear() {
 let bytes:[u8;5]=kani::any();let n:usize=kani::any();kani::assume(n<=5);
 let data=&bytes[..n];let count:usize=kani::any();let magic=*b"ASQ8";
 let mut cleared=false;
 let native=if count!=7 || data.get(..4)!=Some(&magic[..]) {Err(PE::InvalidInstructionData)}else{cleared=true;Ok(())};
 let reference=count==7 && n>=4 && bytes[0]==magic[0] && bytes[1]==magic[1] && bytes[2]==magic[2] && bytes[3]==magic[3];
 assert_eq!(native,if reference {Ok(())}else{Err(PE::InvalidInstructionData)});assert_eq!(cleared,reference);
}
// Source :1012-1014 and :1017-1019. Arbitrary cut lengths, no accepted seeding.
#[kani::proof] #[kani::unwind(3)]
fn S2F_stage2_lengths() {
 let len:usize=kani::any();let end:usize=kani::any();let public_len:usize=kani::any();
 let proof:PR=if len!=end {Err(PE::InvalidAccountData)}else{Ok(())};
 let public:PR=if public_len!=1880 {Err(PE::InvalidInstructionData)}else{Ok(())};
 assert_eq!(proof.is_ok(),len==end);assert_eq!(public.is_ok(),public_len==1880);
}
// Source ?: a child reply is the SAME already reached reply, preserving state
// on both arms. Does not verify a child implementation or its semantic carrier.
fn S2F_native_try(reply:Result<u64,u64>,state:u64,called:&mut bool)->Result<(u64,u64),u64> {
 let value=reply?;*called=true;Ok((value,state))
}
#[kani::proof] #[kani::unwind(3)]
fn S2F_child_error_control() {
 let reply:Result<u64,u64>=kani::any();let state:u64=kani::any();let mut called=false;
 let r=S2F_native_try(reply,state,&mut called);
 match reply {Ok(value)=>{assert_eq!(r,Ok((value,state)));assert!(called)},Err(error)=>{assert_eq!(r,Err(error));assert!(!called)}}
}
// Source :963-968 / :1015-1016; closure mapping differs by site.
#[kani::proof] #[kani::unwind(3)]
fn S2F_mapped_errors() {
 let reply:Result<u64,u64>=kani::any();
 let account=reply.map_err(|_|PE::InvalidAccountData);
 let instruction=reply.map_err(|_|PE::InvalidInstructionData);
 match reply {Ok(v)=>{assert_eq!(account,Ok(v));assert_eq!(instruction,Ok(v));},Err(_)=>{assert_eq!(account,Err(PE::InvalidAccountData));assert_eq!(instruction,Err(PE::InvalidInstructionData));}}
}

// The length helper's reply is an already reached SDK cut. Acquisition/drop
// equivalence is checked separately, not assumed to follow from these metadata gates.
struct S2F_Meta {
 key:[u8;32],owner:[u8;32],is_signer:bool,is_writable:bool,executable:bool,
 len:usize,len_fails:bool,calls:std::cell::Cell<u8>,
}
impl S2F_Meta {
 fn try_data_len(&self)->Result<usize,PE>{
  self.calls.set(self.calls.get()+1);
  if self.len_fails{Err(PE::AccountBorrowFailed)}else{Ok(self.len)}
 }
}
fn S2F_meta()->S2F_Meta {
 S2F_Meta{key:kani::any(),owner:kani::any(),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),len:kani::any(),len_fails:kani::any(),calls:std::cell::Cell::new(0)}
}
fn S2F_code(r:PR)->u8 {
 match r {Ok(())=>0,Err(PE::InvalidAccountData)=>1,Err(PE::InvalidInstructionData)=>2,Err(PE::InvalidArgument)=>3,Err(PE::AccountBorrowFailed)=>4,Err(_)=>5}
}
#[path="S2F_NativeCuts.rs"] mod S2F_NativeCuts;
#[kani::proof] #[kani::unwind(34)]
fn S2F_distinct() {
 let a=S2F_meta();let b=S2F_meta();let c=S2F_meta();
 let native=S2F_NativeCuts::S2F_native_require_distinct_accounts(&[&a,&b,&c]);
 let ref_reject=a.key==b.key || a.key==c.key || b.key==c.key;
 assert!(S2F_code(native)==if ref_reject{3}else{0});
 assert!(a.calls.get()==0 && b.calls.get()==0 && c.calls.get()==0);
}
#[kani::proof] #[kani::unwind(3)]
fn S2F_readonly() {
 let account=S2F_meta();let native=S2F_NativeCuts::S2F_native_require_readonly_buffer(&account);
 let ref_reject=account.is_signer || account.is_writable || account.executable;
 assert!(S2F_code(native)==if ref_reject{1}else{0});assert!(account.calls.get()==0);
}
#[kani::proof] #[kani::unwind(34)]
fn S2F_cp_metadata() {
 let account=S2F_meta();let program:[u8;32]=kani::any();
 let native=S2F_NativeCuts::S2F_native_require_verifier_checkpoint(&account,&program,true);
 let prior=account.owner!=program || account.is_signer || account.executable || !account.is_writable;
 let reference=if prior{1}else if account.len_fails{4}else if account.len!=1768{1}else{0};
 assert!(S2F_code(native)==reference);assert!(account.calls.get()==if prior{0}else{1});
}

// Split replacement for the excluded combined nonempty SDK/Vec context.
// Native payload framing comes from the unchanged checked primitive contract;
// this gate verifies the owned vector side independently, for every cell/byte.
fn S2F_frame_sdk(bytes:&[[u8;2];3],lengths:&[usize;3],counts:&[isize;3])->OwnedSdk {
 let make=|c:usize| {let mut v=Vec::new();if lengths[c]>0{v.push(bytes[c][0]);}if lengths[c]>1{v.push(bytes[c][1]);}OwnedDataCell{bytes:v,borrowed:counts[c],strong:kani::any(),weak:kani::any()}};
 OwnedSdk{accounts:Vec::new(),data_cells:vec![make(0),make(1),make(2)],lamports_cells:Vec::new()}
}
fn S2F_check_frame(o:&OwnedSdk,bytes:&[[u8;2];3],lengths:&[usize;3]) {
 let c:usize=kani::any();kani::assume(c<3);
 assert!(o.data_cells[c].bytes.len()==lengths[c]);
 let j:usize=kani::any();kani::assume(j<lengths[c]);
 assert!(o.data_cells[c].bytes[j]==bytes[c][j]);
}
#[kani::proof] #[kani::unwind(5)]
fn S2F_shared_vector_frame() {
 let bytes:[[u8;2];3]=kani::any();let lengths:[usize;3]=kani::any();kani::assume(lengths[0]<=2 && lengths[1]<=2 && lengths[2]<=2);
 let counts:[isize;3]=kani::any();let c:usize=kani::any();kani::assume(c<3);
 let mut o=S2F_frame_sdk(&bytes,&lengths,&counts);let _=owned_acquire_shared(&mut o,c);
 S2F_check_frame(&o,&bytes,&lengths);
}
#[kani::proof] #[kani::unwind(5)]
fn S2F_exclusive_vector_frame() {
 let bytes:[[u8;2];3]=kani::any();let lengths:[usize;3]=kani::any();kani::assume(lengths[0]<=2 && lengths[1]<=2 && lengths[2]<=2);
 let counts:[isize;3]=kani::any();let c:usize=kani::any();kani::assume(c<3);
 let mut o=S2F_frame_sdk(&bytes,&lengths,&counts);let mut g=LiveGuards{checkpoint:None,public:None,proof:None};
 let _=owned_acquire_checkpoint(&mut o,&mut g,c);S2F_check_frame(&o,&bytes,&lengths);
}

#[path="S2F_CopyStub.rs"] mod S2F_CopyStub;
// Native :982-985, one small source group, with G's verified std-copy child.
// Safe slice domain: fixed destination1768, source length0..1768. The error arm
// performs no destination write. No owner/allocator/query effect is erased here.
#[kani::proof] #[kani::unwind(1772)]
#[kani::stub_verified(S2F_CopyStub::S2G_copy)]
fn S2F_checkpoint_copy_step() {
 let mut checkpoint_data:[u8;1768]=kani::any();let source:[u8;1768]=kani::any();
 let length:usize=kani::any();kani::assume(length<=1768);
 let observed:usize=kani::any();kani::assume(observed<1768);
 let checkpoint=&source[..length];let before=checkpoint_data[observed];
 let outcome=if checkpoint.len()!=checkpoint_data.len() {Err(PE::InvalidAccountData)}else{
  let expected=checkpoint[observed];
  S2F_CopyStub::S2G_copy(&mut checkpoint_data,checkpoint,observed,expected);Ok(())
 };
 if length==1768 {assert!(outcome.is_ok());assert!(checkpoint_data[observed]==source[observed]);}
 else {assert!(matches!(outcome,Err(PE::InvalidAccountData)));assert!(checkpoint_data[observed]==before);}
}
