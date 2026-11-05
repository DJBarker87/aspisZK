from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;p=E/'NGX_native.rs.txt';s=p.read_text();assert 'struct NewOracle' not in s
s+='''
struct NewOracle { calls:usize, root:[u8;32],reply:[u8;32],payload:*const u8,length:usize }
#[derive(Clone,Copy)] struct NewHash<'a>(&'a core::cell::RefCell<NewOracle>);
impl aspis_core::Digest32 for NewHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let mut o=self.0.borrow_mut();assert_eq!(o.calls,0);assert_eq!(parts.len(),5);
  assert_eq!(parts[0],DOMAIN);assert_eq!(parts[1],&[0]);
  assert_eq!(parts[2],&(o.length as u32).to_le_bytes());
  assert_eq!(parts[3].as_ptr(),o.payload);assert_eq!(parts[3].len(),o.length);
  assert_eq!(parts[4],&o.root);o.calls+=1;o.reply
 }
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn new_value() {
 let root:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let length:usize=kani::any();kani::assume(length<=57607);
 let mut public=alloc::vec![0u8;length];let k:usize=kani::any();if length>0 {kani::assume(k<length);public[k]=kani::any();}let oldbyte=if length>0 {public[k]}else{0};
 let local=core::cell::RefCell::new(NewOracle{calls:0,root,reply,payload:public.as_ptr(),length});
 let out=SemanticTranscript::new(NewHash(&local),&public,&root).unwrap();let i:usize=kani::any();kani::assume(i<32);
 assert!((out.state[i]==reply[i])!=cfg!(NGX_invert));assert_eq!(out.next_row,0);assert!(core::ptr::eq(out.hash.0,&local));assert_eq!(local.borrow().calls,1);if length>0 {assert_eq!(public[k],oldbyte);}
}
// Exact first stage of frozen new, lifted to an arbitrary length to cover the
// otherwise physically unallocatable >u32 rejection. No byte is fabricated.
fn new_length(length:usize)->Result<u32,Error> {let length=u32::try_from(length).map_err(|_|Error::Public)?;Ok(length)}
#[kani::proof]
fn new_length_value() {
 let length:usize=kani::any();let got=new_length(length);
 if length>u32::MAX as usize {assert!((matches!(got,Err(Error::Public)))!=cfg!(NGX_invert));}
 else {assert!((got==Ok(length as u32))!=cfg!(NGX_invert));}
}
'''
p.write_text(s);o=json.loads((E/'NGX_OVERLAY.json').read_text());(E/'NGX_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256((E/n).read_bytes()).hexdigest() for p,n in o.items()},indent=1))
