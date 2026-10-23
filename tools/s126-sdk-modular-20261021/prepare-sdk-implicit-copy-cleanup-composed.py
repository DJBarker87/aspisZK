#!/usr/bin/env python3
"""Compose the checked std-copy frame with the actual implicit cleanup.
The timed-out predecessor inlined both the large copy and all typed Drops.
Here only the already checked u8/1768 std-copy contract is used; all SDK and
implicit Drop bodies remain actual. No narrowed statement or opaque guard.
Release allocator dispatch/runtime qualifications remain explicit.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-implicit-copy-cleanup-frame.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();before=s
C=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-parent-cuts/sources/sdk-std-copy-frame-v1/src/lib.rs';c=C.read_text()
a=c.index(' static mut OBSERVED:');b=c.index(' #[kani::proof] #[kani::unwind(8)]',a);helpers=c[a:b]
needle='#[kani::proof_for_contract(ordered_cleanup)]';assert s.count(needle)==1;s=s.replace(needle,helpers+'\n'+needle,1)
needle='fn actual_sdk_ordered_cleanup(){';assert s.count(needle)==1;s=s.replace(needle,'#[kani::stub(<[u8]>::copy_from_slice,copy_bridge)]\n#[kani::stub_verified(verified_byte_copy)]\n'+needle,1)
needle=' let destination=checkpoint_data.as_mut_ptr().cast::<[u8;1768]>();';assert s.count(needle)==1;s=s.replace(needle,' unsafe{OBSERVED=0;EXPECTED=reply[0];}\n'+needle,1)
# Actual accepted source operation and compiler implicit destruction are exact.
def body(src,name):
 a=src.index('fn '+name+'(');b=src.index('{',a)+1;d=1
 while d:d+=(src[b]=='{')-(src[b]=='}');b+=1
 return src[a:b]
for name in ['ordered_cleanup','implicit_cleanup']:assert body(before,name)==body(s,name)
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('implicit-copy-cleanup-frame-v1','implicit-copy-cleanup-composed-v2'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),copy_contract_source=str(C.relative_to(R)),copy_contract_source_sha256=hashlib.sha256(c.encode()).hexdigest(),copy_helpers_verbatim=True,implicit_body_unchanged=True,qualification=__doc__,expected_time='Optimized cached compilation then parent frame enforcement with verified actual std-copy footprint and direct actual implicit destructor bodies. No resource increase;180s solver deadline.',remaining='All parent/precondition/frame/safety checks and covers must pass. Verify same copy contract/source/tool/class instantiation and specialized bridge. Native source accepted-length cut, concrete regions/typed move+cleanup order and full initial native/reference/caller/runtime/oracle/TX2 join remain. Not whole S2.'),indent=2)+'\n')
