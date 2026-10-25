#![allow(static_mut_refs)]
use super::*;
type Row=[QM31;29];
type Claims=[Row;3];
static mut ROWS:Claims=[[QM31::ZERO;29];3];
static mut FAIL_AT:usize=3;
static mut ERROR:Error=Error::Public;
static mut CALLS:usize=0;
static mut FRAME_PTR:*const u8=core::ptr::null();
static mut FRAME_LEN:usize=0;
fn decode_stub<'a,const N:usize>(record:&wire::ValidatedRecord<'a>,offset:usize)->Result<[QM31;N],Error> where 'a:'a {
 unsafe {
  let p=CALLS;
  assert!(N==29);assert!(p<3);assert!(offset==p*29);
  assert!(record.row()==25);assert!(record.framed().as_ptr()==FRAME_PTR);assert!(record.framed().len()==FRAME_LEN);
  CALLS=p+1;
  if p==FAIL_AT{return Err(ERROR);}
  let mut row=[QM31::ZERO;N];let mut i=0;while i<N{row[i]=ROWS[p][i];i+=1;}Ok(row)
 }
}
fn raw_row()->Row{
 let mut row=[QM31::ZERO;29];let mut i=0;
 while i<29{row[i]=QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(kani::any::<u32>()),b:aspis_core::field::M31(kani::any::<u32>())},c1:aspis_core::field::CM31{a:aspis_core::field::M31(kani::any::<u32>()),b:aspis_core::field::M31(kani::any::<u32>())}};i+=1;}
 row
}
fn any_error()->Error{
 match kani::any::<u8>()%11{
  0=>Error::Allocation,1=>Error::RowOrder{expected:kani::any(),actual:kani::any()},2=>Error::InvalidRow,
  3=>Error::Tag{row:kani::any()},4=>Error::Length{row:kani::any()},5=>Error::NonCanonical{row:kani::any(),value:kani::any()},
  6=>Error::Boundary{round:kani::any()},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public,
 }
}


// Explicit COMMON allocator interface; not an actual SDK allocator binding.
// The allocation cut uses zeroed fresh storage on success. No initialization
// property or arbitrary prior heap contents are inferred from this model.
use alloc::alloc::Layout;
static mut ALLOCATION_FAILS:bool=false;
static mut ALLOCATIONS:usize=0;
static mut DEALLOCATIONS:usize=0;
static mut ALLOCATION:*mut u8=core::ptr::null_mut();
unsafe fn allocation_cut(layout:Layout)->*mut u8{unsafe{
 assert!(ALLOCATIONS==0);assert!(layout.size()==1392);assert!(layout.align()==4);
 ALLOCATIONS=1;
 if ALLOCATION_FAILS{return core::ptr::null_mut();}
 let ptr=alloc::alloc::alloc_zeroed(layout);assert!(!ptr.is_null());ALLOCATION=ptr;ptr
}}
unsafe fn deallocation_cut(ptr:*mut u8,layout:Layout){unsafe{
 assert!(!ALLOCATION_FAILS);assert!(ALLOCATIONS==1);assert!(DEALLOCATIONS==0);
 assert!(ptr==ALLOCATION);assert!(layout.size()==1392);assert!(layout.align()==4);
 DEALLOCATIONS=1;
 // Explicit no-op deallocation interface. The frozen Bump dealloc empty-frame
 // fact exists separately; concrete target dispatch/runtime association is OPEN.
}}
unsafe fn reallocation_cut(_ptr:*mut u8,_layout:Layout,_size:usize)->*mut u8{
 assert!(false);core::ptr::null_mut()
}
fn observe(result:Result<Box<Claims>,Error>)->Result<Claims,Error>{
 match result{
  Err(e)=>Err(e),
  Ok(value)=>{unsafe{assert!((&*value as *const Claims).cast::<u8>()as *mut u8==ALLOCATION);}
   let data=*value;drop(value);Ok(data)
  }
 }
}
fn setup(rows:Claims,fail_at:usize,error:Error,frame:&[u8],fail_allocation:bool){unsafe{
 ROWS=rows;FAIL_AT=fail_at;ERROR=error;CALLS=0;FRAME_PTR=frame.as_ptr();FRAME_LEN=frame.len();
 ALLOCATION_FAILS=fail_allocation;ALLOCATIONS=0;DEALLOCATIONS=0;ALLOCATION=core::ptr::null_mut();
}}
fn paired_case(fail_allocation:bool){
 let rows=[raw_row(),raw_row(),raw_row()];let fail_at=(kani::any::<u8>()%4)as usize;let error=any_error();
 let frame=[0u8;3717];let length=(kani::any::<u16>()as usize)%3718;
 let framed=match frame.get(..length){Some(v)=>v,None=>{assert!(false);return;}};
 let root=[0u8;32];let prefix=wire::s1_claims_probe_prefix(&root,framed);
 setup(rows,fail_at,error,framed,fail_allocation);
 let original=observe(crate::original_claims::run(&prefix));
 let first_calls=unsafe{CALLS};let first_frees=unsafe{DEALLOCATIONS};
 assert!(unsafe{ALLOCATIONS}==1);
 setup(rows,fail_at,error,framed,fail_allocation);
 let candidate=observe(claims(&prefix));
 let second_calls=unsafe{CALLS};let second_frees=unsafe{DEALLOCATIONS};
 assert!(unsafe{ALLOCATIONS}==1);assert!(first_calls==second_calls);assert!(first_frees==second_frees);
 if fail_allocation{
  assert!(first_calls==0);assert!(first_frees==0);
  assert!(matches!(original,Err(Error::Allocation)));assert!(matches!(candidate,Err(Error::Allocation)));
 }else{assert!(first_frees==1);assert!(first_calls>0);}
 let mut success=false;
 match (original,candidate){
  (Err(a),Err(b))=>{assert!(a==b);}
  (Ok(a),Ok(b))=>{
   let mut p=0;while p<3{let mut i=0;while i<29{
    assert!(a[p][i].c0.a==b[p][i].c0.a);assert!(a[p][i].c0.b==b[p][i].c0.b);
    assert!(a[p][i].c1.a==b[p][i].c1.a);assert!(a[p][i].c1.b==b[p][i].c1.b);i+=1;}p+=1;}
   success=true;
  }
  _=>{assert!(false);}
 }
 if fail_allocation{kani::cover!(first_calls==0&&first_frees==0,"common allocation failure before decoder");}
 else{
  kani::cover!(fail_at==0&&first_calls==1,"first decode error with one deallocation");
  kani::cover!(fail_at==2&&first_calls==3,"third decode error with one deallocation");
  kani::cover!(success,"full equal result then one deallocation per owner");
 }
}
#[kani::proof]
#[kani::unwind(32)]
#[kani::stub(crate::r1_wire::ValidatedRecord::decode_k,decode_stub)]
#[kani::stub(alloc::alloc::alloc,allocation_cut)]
#[kani::stub(alloc::alloc::dealloc,deallocation_cut)]
#[kani::stub(alloc::alloc::realloc,reallocation_cut)]
fn loop_unrolled(){paired_case(kani::any::<bool>())}
