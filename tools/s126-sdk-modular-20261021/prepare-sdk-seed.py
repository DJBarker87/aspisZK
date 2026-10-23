#!/usr/bin/env python3
"""Check the exact native harness prefix/tag initializer against its byte image.
This is a harness-domain transport, not a production source change.
"""
from pathlib import Path
import sys,json,hashlib
out=Path(sys.argv[1]);(out/'src').mkdir(parents=True,exist_ok=False)
s='''#![allow(dead_code,unexpected_cfgs)]
pub fn seed_byte(original:u8,candidate:u8,index:usize)->u8 {
 if index<688 {candidate} else if index==696 {2} else {original}
}
#[cfg(kani)] struct Ghost<T>{value:T,tag:u64}
#[cfg(kani)] static mut OBSERVED:Ghost<usize>=Ghost{value:0,tag:0x51a3000000000001};
#[cfg(kani)] static mut EXPECTED:Ghost<u8>=Ghost{value:0,tag:0x51a3000000000002};
#[cfg(kani)] fn observed()->usize {unsafe{OBSERVED.value}}
#[cfg(kani)] fn expected()->u8 {unsafe{EXPECTED.value}}
#[cfg_attr(kani,kani::requires(observed()<58295))]
#[cfg_attr(kani,kani::requires(expected()==seed_byte(bytes[observed()],if observed()<688 {candidate[observed()]}else{0},observed())))]
#[cfg_attr(kani,kani::modifies(bytes.as_mut_ptr().cast::<[u8;688]>(),unsafe{bytes.as_mut_ptr().add(696)}))]
#[cfg_attr(kani,kani::ensures(|_| bytes[observed()]==expected()))]
pub fn native_seed(bytes:&mut [u8;58295],candidate:&[u8;688]) {
 unsafe{core::ptr::copy_nonoverlapping(candidate.as_ptr(),bytes.as_mut_ptr(),688);}
 bytes[696]=2;
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(native_seed)] #[kani::unwind(8)]
 fn native_seed_byte_and_frame() {
  let mut bytes:[u8;58295]=kani::any();let candidate:[u8;688]=kani::any();
  let index:usize=kani::any();kani::assume(index<58295);
  let old=bytes[index];let selected=if index<688 {candidate[index]}else{0};
  let want=seed_byte(old,selected,index);
  unsafe{OBSERVED.value=index;EXPECTED.value=want;}
  native_seed(&mut bytes,&candidate);
  assert_eq!(bytes[index],want);
  kani::cover!(index==0,"prefix begins");
  kani::cover!(index==687,"prefix ends");
  kani::cover!(index==696,"tag cell");
  kani::cover!(index==58294,"last unchanged byte");
 }
}
'''
prefix_view='prefix-view' in sys.argv[2:]
if prefix_view:
 s=s.replace('#[cfg_attr(kani,kani::requires(observed()<58295))]', '''fn prefix_value(bytes:&[u8;58295],index:usize)->u8 {
  let prefix=unsafe{core::ptr::read(bytes.as_ptr().cast::<[u8;688]>())};
  prefix[index]
}
#[cfg_attr(kani,kani::requires(observed()<688))]''')
 s=s.replace('expected()==seed_byte(bytes[observed()],if observed()<688 {candidate[observed()]}else{0},observed())','expected()==candidate[observed()]')
 s=s.replace('bytes[observed()]==expected()', 'prefix_value(bytes,observed())==expected() && bytes[696]==2')
 s=s.replace('kani::assume(index<58295);','kani::assume(index<688);')
 s=s.replace('let old=bytes[index];let selected=if index<688 {candidate[index]}else{0};','let old=0;let selected=candidate[index];')
 s=s.replace('assert_eq!(bytes[index],want);','assert_eq!(prefix_value(&bytes,index),want);assert_eq!(bytes[696],2);')
 s=s.replace('  kani::cover!(index==696,"tag cell");\n  kani::cover!(index==58294,"last unchanged byte");\n','')
frame_only='frame-only' in sys.argv[2:]
if frame_only:
 start=s.index('#[cfg_attr(kani,kani::requires(observed()<58295))]')
 stop=s.index('pub fn native_seed',start)
 s=s[:start]+'''#[cfg_attr(kani,kani::modifies(bytes.as_mut_ptr().cast::<[u8;688]>(),unsafe{bytes.as_mut_ptr().add(696)}))]
#[cfg_attr(kani,kani::ensures(|_| bytes[696]==2))]
'''+s[stop:]
 start=s.index('  let index:usize=kani::any();')
 stop=s.index(' }\n}',start)
 s=s[:start]+'''  native_seed(&mut bytes,&candidate);
  assert_eq!(bytes[696],2);
  kani::cover!(bytes[696]==2,"initializer returns with tag2");
'''+s[stop:]
(out/'src/lib.rs').write_text(s)
(out/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-seed"
version="0.0.0"
edition="2021"
[workspace]
[profile.release]
opt-level=3
overflow-checks=true
''')
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,domain='All58295-byte proof buffers, all688-byte candidates and every observed coordinate0..58294. Exact native raw copy688 plus byte696=2, precise prefix-and-tag write set and exact pointwise output. Same operation sequence as the accepted native caller harness. Full caller transport and accepted-guard identity require separate composition.'),indent=2)+'\n')
if prefix_view:
 p=out/'source-cut.json';m=json.loads(p.read_text());m['domain']='All58295-byte proof buffers and all688-byte candidates. Prefix output checked at arbitrary coordinate0..687 through an actual typed688-byte prefix view, fixed tag696 checked, precise write set permits only prefix688 and tag696. Other bytes are protected by the write-frame certificate, not queried with a large dynamic index. Native raw-copy/tag statements unchanged; accepted-guard identity and enclosing caller transport remain separate.';p.write_text(json.dumps(m,indent=2)+'\n')
if frame_only:
 p=out/'source-cut.json';m=json.loads(p.read_text());m['domain']='All58295-byte proof buffers and all688-byte candidates. Check only exact prefix688/tag696 write set and fixed tag postcondition; no dynamic byte read or prefix-value postcondition. Native raw-copy/tag statements unchanged. Functional prefix and enclosing caller composition remain unproved.';p.write_text(json.dumps(m,indent=2)+'\n')
