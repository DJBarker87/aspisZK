#!/usr/bin/env python3
"""Enforce actual native caller write frame without full-buffer value muxes.
The failed predecessor observed arbitrary58295-byte coordinates and timed out.
This target instead enforces the exact write footprint of the ORIGINAL native
SDK/copy/implicit-cleanup body. All statement/output allocations are created
inside that checked caller. No SDK/copy/Drop verified/model stubs; pure child,
scan/comparison ports and source-reached control domain remain explicit.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-success-bytes-pair.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();needle='fn native_prefix(';a=s.index(needle)
frame='''#[kani::modifies(
 unsafe{NATIVE_ROOT_PTRS.value[2].cast_mut().cast::<[u8;1768]>()},
 unsafe{COUNTERS.value[0].cast_mut().cast::<isize>()},
 unsafe{COUNTERS.value[1].cast_mut().cast::<isize>()},
 unsafe{COUNTERS.value[2].cast_mut().cast::<isize>()},
 unsafe{std::ptr::addr_of_mut!(CALLS.value)},
 unsafe{std::ptr::addr_of_mut!(BOX_PTRS.value)},
 unsafe{std::ptr::addr_of_mut!(CANDIDATE_PTRS.value)},
 unsafe{std::ptr::addr_of_mut!(PUBLIC_KIND.value)},
 unsafe{std::ptr::addr_of_mut!(PUBLIC_PARTS.value)},
 unsafe{std::ptr::addr_of_mut!(CMP_CALLS.value)}
)]
'''
s=s[:a]+frame+s[a:]
s=s.replace('#[kani::proof] #[kani::unwind(48)]','#[kani::proof_for_contract(native_prefix)] #[kani::unwind(48)]',1)
s=s.replace(' let mut checkpoint_initial=Some(buffers[2].clone());\n','')
a=s.index(' // Native handles are gone.');s=s[:a]+'''
 kani::cover!(actual.is_ok(),"original full native caller successful write-frame case");
 kani::cover!(actual.is_err(),"original full native caller rejection write-frame case");
}
}
'''
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('success-bytes-pair-v1','native-write-frame-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,frame=frame,expected_time='Cached optimized compilation then actual native full-write-frame enforcement, with full proof/public coordinate reads removed and reference second execution removed. Original copy/implicit cleanup execute; fresh allocations belong to checked function. No resource cap increase.',remaining='All assertions and covers must pass. Concretely identify allowed checkpoint/counter regions, derive original input-byte identities and compose with green unseeded complete native/reference pair. Source-control, pure-child/scan/comparison and valid runtime/ABI/allocator/oracle/TX2 transport remain. No whole S2 claim.'),indent=2)+'\n')
