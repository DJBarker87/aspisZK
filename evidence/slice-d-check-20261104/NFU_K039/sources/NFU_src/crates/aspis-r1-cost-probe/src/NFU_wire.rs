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
