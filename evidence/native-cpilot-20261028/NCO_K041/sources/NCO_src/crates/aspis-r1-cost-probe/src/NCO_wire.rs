use super::*;
#[path="NCO_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(row_shape)]
fn shape_contract(){let _=row_shape(kani::any());}
#[kani::proof] #[kani::stub_verified(row_shape)]
fn shape_caller(){let row:u8=kani::any();assert_eq!(row_shape(row),reference::row_shape_ref(row));}
#[kani::proof] #[kani::stub_verified(row_shape)]
fn shape_caller_wrong(){let row:u8=kani::any();assert_ne!(row_shape(row),reference::row_shape_ref(row));}
pub(super) pub(super) fn matches_ref(a:&Result<&[u8],Error>,b:&Result<&[u8],reference::RefError>)->bool{
 match (a,b){
  (Ok(x),Ok(y))=>core::ptr::eq(*x,*y),
  (Err(Error::InvalidRow),Err(reference::RefError::InvalidRow))=>true,
  (Err(Error::Length{row:a}),Err(reference::RefError::Length(b)))=>a==b,
  (Err(Error::Tag{row:a}),Err(reference::RefError::Tag(b)))=>a==b,
  (Err(Error::NonCanonical{row:a,value:i}),Err(reference::RefError::NonCanonical(b,j)))=>a==b && i==j,
  _=>false,
 }
}
#[kani::proof_for_contract(parse_record)]
fn parse_contract(){
 #[cfg(NCO_header)] let data:[u8;5]=kani::any();
 #[cfg(not(NCO_header))] let data:[u8;37]=kani::any();
 let n:usize=kani::any();let row:u8=kani::any();
 kani::assume(n<=data.len() && row<14);
 #[cfg(NCO_payload)] kani::assume(row==2 && n==37);
 let _=parse_record(row,&data[..n]);
}
#[kani::proof] #[kani::stub_verified(row_shape)]
fn parse_with_shape(){let data:[u8;37]=kani::any();let n:usize=kani::any();let row:u8=kani::any();kani::assume(n<=37 && row<14);assert!(matches_ref(&parse_record(row,&data[..n]),&reference::parse_record_ref(row,&data[..n])));}
#[kani::proof] #[kani::stub_verified(parse_record)]
fn parse_callsite(){let data:[u8;37]=kani::any();let n:usize=kani::any();let row:u8=kani::any();kani::assume(n<=37 && row<14);assert!(matches_ref(&parse_record(row,&data[..n]),&reference::parse_record_ref(row,&data[..n])));}
#[kani::proof_for_contract(parse_record_at)] #[kani::stub_verified(parse_record)] #[kani::stub_verified(row_shape)]
fn parse_at_contract(){let data:[u8;42]=kani::any();let off:usize=kani::any();let row:u8=kani::any();kani::assume(off<=5 && row<14);let _=parse_record_at(&data,row,off);}
