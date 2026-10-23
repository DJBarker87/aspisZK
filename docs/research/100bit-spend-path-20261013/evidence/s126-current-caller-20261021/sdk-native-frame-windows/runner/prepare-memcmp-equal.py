#!/usr/bin/env python3
"""Specialized688-byte equality case of the actual CBMC/libc memcmp boundary.
Scalar content equality is the precondition, not a second call to memcmp.
Same-pointer and distinct owned-array instances are checked; transport to every
caller/heap layout and any eventual replacement must remain explicit.
"""
from pathlib import Path
import json,hashlib,sys
O=Path(sys.argv[1]);(O/'src').mkdir(exist_ok=True,parents=True)
s='''#![allow(dead_code,unexpected_cfgs)]
use aspis_s126_sdk_proof_gate::prefix_different;
extern "C" {#[link_name="memcmp"] fn native_memcmp(left:*const u8,right:*const u8,length:usize)->i32;}
#[cfg_attr(kani,kani::requires(!prefix_different(left,right)))]
#[cfg_attr(kani,kani::modifies())]
#[cfg_attr(kani,kani::ensures(|result| *result==0))]
pub fn equal_memcmp(left:&[u8;688],right:&[u8;688])->i32 {
 unsafe{native_memcmp(left.as_ptr(),right.as_ptr(),688)}
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(equal_memcmp)] #[kani::unwind(700)]
 fn native_equal_arrays_memcmp() {
  let left:[u8;688]=kani::any();let right=left;
  let alias:bool=kani::any();
  let selected=if alias {&left}else{&right};
  let actual=equal_memcmp(&left,selected);
  assert_eq!(actual,0);
  kani::cover!(alias,"same-pointer equal688-byte regions");
  kani::cover!(!alias,"distinct equal688-byte regions");
 }
}
'''
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-memcmp-equal"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
aspis-s126-sdk-proof-gate={path="/home/dombarker/project-offloads/s126-real-sdk-20261021/sdk-proof-gate-v1"}
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,domain='Every688-byte value; one same-start pointer or two distinct owned array objects carrying equal values. Precondition uses the previously extracted scalar prefix loop. Actual native C ABI memcmp and its normal Kani library model execute, with an empty-write-set/zero-return contract. Other pointer/overlap layouts, source caller installation and any C-model replacement remain unproved by this leaf.'),indent=2)+'\n')
