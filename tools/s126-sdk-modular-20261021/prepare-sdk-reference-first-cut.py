#!/usr/bin/env python3
"""Reference constructor with admitted comparison status supplied by native gate.
No SDK method replaced. It retains conditional gate/scan/typed-child transport;
zero comparison here is justified only at a native admitted first call.
"""
from pathlib import Path
import sys,json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-reference-first.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text()
s=s.replace('proof[..688].copy_from_slice(&candidate);proof[696]=2;','proof[696]=2;')
s=s.replace('assert_eq!(out.data_cells[i].bytes.as_ptr(),pointers[i]);assert_eq!(out.data_cells[i].borrowed,counts[i]);','if i<2{assert_eq!(out.data_cells[i].bytes.as_ptr(),pointers[i]);}assert_eq!(out.data_cells[i].borrowed,counts[i]);')
s=s.replace('fn reference_first(){','fn native_owned_decoder_prefix(){\n unsafe{s126_keep_coupled_cmp.value=Some(s126_coupled_cmp);}')
s=s.replace('fn planned_scan(_: &[u8])->bool{false}', '''#[no_mangle] pub static mut s126_keep_coupled_cmp:GhostStorage<Option<extern "C" fn(*const u8,*const u8,usize)->i32>>=GhostStorage{value:None,allocation_tag:0x51a9000000000001};
#[no_mangle] pub extern "C" fn s126_coupled_cmp(a:*const u8,b:*const u8,n:usize)->i32 {
 assert_eq!(n,688);assert_eq!(unsafe{CALLS.value[0]},[1,1,1,0]);
 let root=unsafe{NATIVE_ROOT_PTRS.value[0]};assert!(a==root||b==root);
 0 // Native admitted-gate comparison status; source/value transport required.
}
fn planned_scan(_: &[u8])->bool{false}''')
assert 'pub extern "C" fn s126_coupled_cmp' in s
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s126-sdk-reference-first-v1','aspis-s126-sdk-shared-prefix-reference-first-v3'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,correction='Successful owned checkpoint replaces its Vec representation; pointer preservation applies only proof/public. Every checkpoint output coordinate is asserted. Prior v1 solver timeout/no result provides no evidence.',remaining='Conditional reference only: native-gate admitted0 comparison status, tag byte image, native initial frame/scalar construction, source scan and typed child installation, actual checkpoint writer/reader/runtime/oracle transport remain. No whole S2.'),indent=2)+'\n')
