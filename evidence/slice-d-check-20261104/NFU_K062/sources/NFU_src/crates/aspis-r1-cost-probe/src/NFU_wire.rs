use super::*;
#[kani::proof_for_contract(ValidatedRecord::row)]
fn row_contract(){let bytes:[u8;3717]=kani::any();let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=3717&&len<=3717-start);let r=ValidatedRecord{row:kani::any(),framed:&bytes[start..start+len]};let _=r.row();}
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

include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn frozen_validator_step(row:u8,value:usize,bytes:&[u8])->Result<(),Error>{
        let x = WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
        if x.c1() != QM31::ZERO {
            return Err(Error::NonCanonical { row, value });
        }
Ok(())
}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]

fn validate_step(){let b:[u8;32]=kani::any();let row:u8=kani::any();let value:usize=kani::any();kani::assume(value<116);let mut good=true;for j in 0..4{good&=u32::from_le_bytes([b[4*j],b[4*j+1],b[4*j+2],b[4*j+3]])<0x7fffffff;}for j in 16..32{good&=b[j]==0;}let actual=frozen_validator_step(row,value,&b);let exact=if good{matches!(actual,Ok(()))}else{matches!(actual,Err(Error::NonCanonical{row:r,value:v}) if r==row&&v==value)};assert!(exact != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(3)]
fn validate_iterator(){
 let b:[u8;3712]=kani::any();let n:usize=kani::any();kani::assume(n<=3712);let i:usize=kani::any();kani::assume(i<=n/32);
 let mut it=b[..n].chunks_exact(32).enumerate();if i>0{let _=it.nth(i-1);}
 let mut exact=it.len()==n/32-i;
 match it.next(){None=>exact&=i==n/32,Some((index,part))=>{exact&=index==i&&part.len()==32&&core::ptr::eq(part.as_ptr(),b[32*i..].as_ptr())&&it.len()==n/32-(i+1);}}
 assert!(exact != cfg!(NFU_invert));
}

#[kani::proof] #[kani::unwind(2)]
fn parse_invalid_row(){let b:[u8;3717]=kani::any();let row:u8=kani::any();kani::assume(row>=27);let n:usize=kani::any();kani::assume(n<=3717);assert!(matches!(parse_record(row,&b[..n]),Err(Error::InvalidRow)) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(2)]
fn parse_bad_length(){let b:[u8;3717]=kani::any();let row:u8=kani::any();kani::assume(row<27);let size=row_shape(row).unwrap().1;let n:usize=kani::any();kani::assume(n<=3717&&n!=5+size);assert!(matches!(parse_record(row,&b[..n]),Err(Error::Length{row:r}) if r==row) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(2)]
fn parse_bad_tag(){let b:[u8;3717]=kani::any();let row:u8=kani::any();kani::assume(row<27);let (tag,size)=row_shape(row).unwrap();kani::assume(b[0]!=tag);assert!(matches!(parse_record(row,&b[..5+size]),Err(Error::Tag{row:r}) if r==row) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(validate_record_fields,unreachable_validation)]
fn parse_bad_header(){let mut b:[u8;3717]=kani::any();let row:u8=kani::any();kani::assume(row<27);let (tag,size)=row_shape(row).unwrap();b[0]=tag;kani::assume(u32::from_le_bytes([b[1],b[2],b[3],b[4]]) as usize!=size);assert!(matches!(parse_record(row,&b[..5+size]),Err(Error::Length{row:r}) if r==row) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(2)]
fn parse_at_short(){let b:[u8;13831]=kani::any();let row:u8=kani::any();kani::assume(row<27);let n:usize=kani::any();let offset:usize=kani::any();kani::assume(n<=13831&&offset<=13831);let length=5+row_shape(row).unwrap().1;kani::assume(offset+length>n);assert!(matches!(parse_record_at(&b[..n],row,offset),Err(Error::Length{row:r}) if r==row) != cfg!(NFU_invert));}

fn unreachable_validation(_:u8,_:&[u8])->Result<(),Error>{assert!(false,"header guard must not call validation");Ok(())}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn prefix_record(){let b:[u8;3717]=kani::any();let records:[&[u8];27]=core::array::from_fn(|_|{let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=3717&&len<=3717-start);&b[start..start+len]});let p=Prefix{c1_root:[0;32],records};let row:u8=kani::any();let r=p.record(row);let exact=if row>=27{matches!(r,Err(Error::InvalidRow))}else{match r{Ok(s)=>core::ptr::eq(s.as_ptr(),records[row as usize].as_ptr())&&s.len()==records[row as usize].len(),Err(_)=>false}};assert!(exact != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn prefix_validated(){let b:[u8;3717]=kani::any();let records:[&[u8];27]=core::array::from_fn(|_|{let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=3717&&len<=3717-start);&b[start..start+len]});let p=Prefix{c1_root:[0;32],records};let row:u8=kani::any();let r=p.validated_record(row);let exact=if row>=27{matches!(r,Err(Error::InvalidRow))}else{match r{Ok(s)=>s.row==row&&core::ptr::eq(s.framed.as_ptr(),records[row as usize].as_ptr())&&s.framed.len()==records[row as usize].len(),Err(_)=>false}};assert!(exact != cfg!(NFU_invert));}
