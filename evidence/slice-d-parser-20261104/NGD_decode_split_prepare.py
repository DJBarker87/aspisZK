from pathlib import Path
import json
from NGD_add_inputs import update
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/NGD_wire.rs';s=json.loads((E/'NGD_NATIVE_INPUTS.json').read_text())[p]
s+='''
// Isolated exact scalar prefix; no value decoding or buffer traversal.
#[kani::proof] #[kani::unwind(2)]
fn decode_scalar_all(){
 let b:[u8;3717]=kani::any();let len:usize=kani::any();kani::assume(5<=len&&len<=3717);
 let row:u8=kani::any();let off:usize=kani::any();let n:usize=kani::any();kani::assume(n==1||n==28||n==29);
 let actual=(||->Result<(),Error>{
  if row<14{return Err(Error::InvalidRow);}
  let byte_offset=off.checked_mul(32).ok_or(Error::Length{row})?;
  let byte_len=n.checked_mul(32).ok_or(Error::Length{row})?;
  let end=byte_offset.checked_add(byte_len).ok_or(Error::Length{row})?;
  let _bytes=ValidatedRecord{row,framed:&b[..len]}.payload().get(byte_offset..end).ok_or(Error::Length{row})?;
  Ok(())})();
 let fits=(off as u128)*32+(n as u128)*32<=(len-5)as u128;
 let expected=if row<14{Err(Error::InvalidRow)}else if fits{Ok(())}else{Err(Error::Length{row})};
 assert!((actual==expected) != cfg!(NGD_invert));
}
#[kani::proof] #[kani::unwind(2)]
fn decode_iterator(){
 let b:[u8;3717]=kani::any();let len:usize=kani::any();kani::assume(5<=len&&len<=3717);
 let n:usize=kani::any();kani::assume(n==1||n==28||n==29);let off:usize=kani::any();kani::assume(off<=116&&32*(off+n)<=len-5);
 let i:usize=kani::any();kani::assume(i<=n);
 let record=ValidatedRecord{row:25,framed:&b[..len]};let payload=record.payload();let selected=&payload[32*off..32*(off+n)];
 let mut it=selected.chunks_exact(32).enumerate();if i>0{let(j,_)=it.nth(i-1).unwrap();assert_eq!(j,i-1);}
 let before=it.len();let good=match it.next(){None=>i==n&&before==0,Some((value,part))=>i<n&&value==i&&part.len()==32&&part.as_ptr()==b.as_ptr().wrapping_add(5+32*(off+i))&&before==n-i&&it.len()==n-i-1&&off+value<116};
 assert!(good != cfg!(NGD_invert));
}
fn raw_q()->QM31{QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(kani::any()),b:aspis_core::field::M31(kani::any())},c1:aspis_core::field::CM31{a:aspis_core::field::M31(kani::any()),b:aspis_core::field::M31(kani::any())}}}
fn same_q(a:QM31,b:QM31)->bool{a.c0.a.0==b.c0.a.0&&a.c0.b.0==b.c0.b.0&&a.c1.a.0==b.c1.a.0&&a.c1.b.0==b.c1.b.0}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(QM31::from_le_bytes,NGD_decode_le)]
fn decode_typed_write(){
 let b:[u8;37]=kani::any();let row:u8=kani::any();kani::assume(row>=14);
 let mut out=[raw_q(),raw_q(),raw_q()];let j:usize=kani::any();kani::assume(j<3);let old=out[j];
 let actual=ValidatedRecord{row,framed:&b}.decode_k::<1>(0);let expected=NGD_decode_le(&b[5..21]);
 let good=match(actual,expected){(Ok([q]),Some(v))=>{out[1]=q;same_q(q,v)&&same_q(out[j],if j==1{v}else{old})},(Err(Error::NonCanonical{row:r,value:0}),None)=>r==row&&same_q(out[j],old),_=>false};
 assert!(good != cfg!(NGD_invert));
}
'''
update({p:s},'NGD_decode_split')
