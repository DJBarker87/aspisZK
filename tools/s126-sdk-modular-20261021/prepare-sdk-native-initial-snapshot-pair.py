#!/usr/bin/env python3
"""Complete successful pair from a FULL FIXED reference snapshot built BEFORE native execution.
All proof/public/checkpoint buffers and metadata of the reference are created
from the fixed original inputs before any native SDK call. Real Vec<u8> clones
supply the owned bytes; native SDK/copy/implicit cleanup stay original. Native
and reference first sites retain their respective real input pointers; byte
identity uses initial clone construction, not post-native pointer equality.
No post-native buffer-frame premise or seeded bytes; account-write frame stays
separate. Source-control/pure-child/scan/comparison and runtime/oracle binding
remain explicit; this candidate is not whole S2.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-success-bytes-pair.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text()
for i in [0,1]:
 needle=f'unsafe{{NATIVE_ROOT_PTRS.value[{i}]}}'
 s=s.replace(needle,f'(if phase==0 {{unsafe{{NATIVE_ROOT_PTRS.value[{i}]}}}}else{{unsafe{{MODEL_ROOT_PTRS.value[{i}]}}}})')
a=s.index('  let model=OwnedSdk{');b=s.index('{',a)+1;depth=1
while depth:
 depth+=(s[b]=='{')-(s[b]=='}');b+=1
assert s[b]==';';b+=1;model=s[a:b];s=s[:a]+s[b:]
needle='data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes:if i==2 {checkpoint_initial.take().unwrap()}else{bytes},borrowed:';assert model.count(needle)==1
model=model.replace(needle,'data_cells:model_buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:')
needle=' let mut checkpoint_initial=Some(buffers[2].clone());';assert s.count(needle)==1
s=s.replace(needle,''' let model_buffers=core::array::from_fn::<_,3,_>(|i|buffers[i].clone());
 let model_pointers=core::array::from_fn::<_,3,_>(|i|model_buffers[i].as_ptr());
 unsafe{MODEL_ROOT_PTRS.value=model_pointers;}
'''+model)
s=s.replace('if i<2 {assert_eq!(model.data_cells[i].bytes.as_ptr(),pointers[i],"complete reference preserves original proof/public allocations");}','if i<2 {assert_eq!(model.data_cells[i].bytes.as_ptr(),model_pointers[i],"complete reference retains its FIXED INITIAL owned proof/public snapshots");}')
s=s.replace(' // Native handles are gone. Independent all-root/window frame certificates\n // are required before identifying these bytes with the initial heap.',' // The COMPLETE model state was fixed before native execution.\n // No post-native buffer contents are reused as its initial proof/public inputs.')
assert s.index('let model=OwnedSdk{')<s.index(' let actual={') and 'checkpoint_initial' not in s
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('success-bytes-pair-v1','initial-snapshot-pair-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compilation then complete actual native/reference success with full initial state snapshotted before native, original native copy/implicit cleanup and no SDK/copy/Drop stubs;8G cap unchanged.',remaining='All assertions/covers must pass. Exact native prefix original-input/accepted-control facts and source Vec clone semantics must compose with fixed snapshot construction; actual pure first/decoder/encoder/scan/comparison/runtime/ABI/allocator/oracle/TX2 interpretation and the separate native account frame remain. No whole S2.'),indent=2)+'\n')
