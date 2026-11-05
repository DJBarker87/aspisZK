from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
p=E/'NGX_native.rs.txt'
s=p.read_text()
assert 'struct Oracle' not in s
s+='''
struct Oracle { calls:usize, row:u8, initial:[u8;32], replies:[[u8;32];3], payload:*const u8, length:usize }
struct OracleHash<'a>(&'a core::cell::RefCell<Oracle>);
impl aspis_core::Digest32 for OracleHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let mut o=self.0.borrow_mut();let n=o.calls;assert!(n<3);
  if n==0 {
   assert_eq!(parts.len(),3);assert_eq!(parts[0],&o.initial);
   assert_eq!(parts[1],&[0,160+o.row]);assert_eq!(parts[2].as_ptr(),o.payload);assert_eq!(parts[2].len(),o.length);
  } else {
   assert_eq!(parts.len(),2);assert_eq!(parts[0],&o.replies[0]);assert_eq!(parts[1],&[n as u8]);
  }
  o.calls+=1;o.replies[n]
 }
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn sample_value() {
 let state:[u8;32]=kani::any();let replies:[[u8;32];3]=kani::any();let row:u8=kani::any();kani::assume(row<=26);
 let next:u8=kani::any();let length:usize=kani::any();kani::assume(length<=3717);
 let mut payload=alloc::vec![0u8;length];let k:usize=kani::any();
 if length>0 {kani::assume(k<length);payload[k]=kani::any();}
 let oldbyte=if length>0 {payload[k]}else{0};
 let local=core::cell::RefCell::new(Oracle{calls:0,row,initial:state,replies,payload:payload.as_ptr(),length});
 let mut t=SemanticTranscript{state,hash:OracleHash(&local),next_row:next};
 let out=t.sample_block_validated(row,&payload);
 let i:usize=kani::any();kani::assume(i<32);
 if row!=next {assert!(matches!(out,Err(Error::RowOrder{expected,actual}) if expected==next&&actual==row));assert_eq!(local.borrow().calls,0);assert_eq!(t.state[i],state[i]);assert_eq!(t.next_row,next);}
 else {let out=out.unwrap();assert!((out[i]==replies[1][i])!=cfg!(NGX_invert));assert_eq!(t.state[i],replies[2][i]);assert_eq!(t.next_row,row+1);assert_eq!(local.borrow().calls,3);}
 assert!(core::ptr::eq(t.hash.0,&local));if length>0 {assert_eq!(payload[k],oldbyte);}
}
'''
p.write_text(s)
o=json.loads((E/'NGX_OVERLAY.json').read_text());(E/'NGX_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256((E/n).read_bytes()).hexdigest() for p,n in o.items()},indent=1))
