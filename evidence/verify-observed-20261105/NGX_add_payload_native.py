from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;p=E/'NGX_native.rs.txt';s=p.read_text();assert 'fn payload_value()' not in s
s+='''
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn payload_value() {
 let backing=alloc::vec![0u8;17000];
 let records:[&[u8];27]=core::array::from_fn(|_|{let start:usize=kani::any();let length:usize=kani::any();kani::assume(start<=13000&&length>=5&&length<=3717);&backing[start..start+length]});
 let root:&[u8;32]=(&backing[..32]).try_into().unwrap();
 let p=Prefix{c1_root:root,records};let row:u8=kani::any();let got=p.payload(row);
 if row>=27 {assert!(matches!(got,Err(Error::InvalidRow)));}
 else {let original=p.records[row as usize];let out=got.unwrap();assert_eq!(out.as_ptr(),unsafe{original.as_ptr().add(5)});assert!((out.len()==original.len()-5)!=cfg!(NGX_invert));}
}
'''
p.write_text(s);o=json.loads((E/'NGX_OVERLAY.json').read_text());(E/'NGX_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256((E/n).read_bytes()).hexdigest() for p,n in o.items()},indent=1))
