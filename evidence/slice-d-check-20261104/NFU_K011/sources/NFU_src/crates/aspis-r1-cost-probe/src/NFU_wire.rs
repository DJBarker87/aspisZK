use super::*;
#[kani::proof_for_contract(ValidatedRecord::row)]
fn row_contract(){let row:u8=kani::any();let r=ValidatedRecord{row,framed:&[]};let _=r.row();}
// Borrowed-return association: same typed slice, no copy, allocation or mutation.
#[kani::proof]
fn framed_identity(){let bytes:[u8;3717]=kani::any();let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=3717&&len<=3717-start);let input=&bytes[start..start+len];let record=ValidatedRecord{row:kani::any(),framed:input};let result=record.framed();assert!((result.as_ptr()==input.as_ptr()&&result.len()==input.len()) != cfg!(NFU_invert));}
#[kani::proof]
fn payload_identity(){let bytes:[u8;3717]=kani::any();let len:usize=kani::any();kani::assume(5<=len&&len<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..len]};let result=r.payload();assert!((result.as_ptr()==unsafe{bytes.as_ptr().add(5)}&&result.len()==len-5) != cfg!(NFU_invert));}

#[kani::ensures(|r| *r<=2)] #[kani::modifies()]
fn weak_u8()->u8{1}
#[kani::proof_for_contract(weak_u8)]
fn u8_real(){assert_eq!(weak_u8(),1);}
#[kani::proof] #[kani::stub_verified(weak_u8)]
fn u8_unimplied(){assert_eq!(weak_u8(),1);}
#[kani::ensures(|r| *r==1)] #[kani::modifies(&mut x[0])]
fn bad_u8_frame(x:&mut[u8;2])->u8{x[1]=x[1].wrapping_add(1);1}
#[kani::proof_for_contract(bad_u8_frame)]
fn u8_frame(){let mut x:[u8;2]=kani::any();let _=bad_u8_frame(&mut x);}
