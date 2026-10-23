#!/usr/bin/env python3
"""Actual complete native/reference successful caller pairing, necessary image.
Both complete bodies execute with original SDK, full typed statement and arbitrary
common1768-byte first reply. Original native copy and implicit cleanup execute:
no SDK/copy/Drop verified stubs or explicit-cleanup source candidate. Same original
proof/public allocations; model checkpoint starts from the SAME initial zero byte
image in its owned buffer, not the native already-written output. Normalization,
source pure-child/scan/comparison and valid runtime/oracle bindings remain gates.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-first-image-pair.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text()
s=s.replace('candidate:[u8;688],k:usize','candidate:[u8;688],output:[u8;1768],k:usize')
s=s.replace('candidate:kani::any(),k:instruction[1] as usize','candidate:kani::any(),output:kani::any(),k:instruction[1] as usize')
assert 'output:kani::any()' in s
s=s.replace('Ok(Vec::new())','Ok(plan().output.to_vec())')
s=s.replace('#[kani::stub(<[u8]>::copy_from_slice,unreachable_copy)]\n','')
assert '#[kani::stub(<[u8]>::copy_from_slice' not in s
needle=' let cmp_index:usize=kani::any();kani::assume(cmp_index<688);';assert s.count(needle)==1
s=s.replace(needle,needle+'\n let checkpoint_index:usize=kani::any();kani::assume(checkpoint_index<1768);')
s=s.replace(' assert!(actual.is_err());',' if unsafe{CALLS.value[0]}==[1,1,1,1] {assert!(actual.is_ok());\n assert_eq!(unsafe{(*pointers[2].add(checkpoint_index))},plan().output[checkpoint_index],"actual complete native source saved the common first checkpoint byte");}')
s=s.replace('data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:', 'data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes:if i==2 {vec![0;1768]}else{bytes},borrowed:')
a=s.index('  assert!(matches!(&actual,Err(ProgramError::InvalidAccountData)');b=s.index('  assert_eq!(unsafe{CALLS.value[0]}',a)
s=s[:a]+'''  assert!(actual.is_ok()&&expected.is_ok(),"actual complete native success constructs complete borrowed-reference success");
  assert_eq!(model.data_cells[2].bytes[checkpoint_index],plan().output[checkpoint_index],"complete borrowed reference saved the SAME first checkpoint byte");
'''+s[b:]
s=s.replace('assert_eq!(model.data_cells[i].bytes.as_ptr(),pointers[i],"reference preserves the original allocation, not a copied carrier");','if i<2 {assert_eq!(model.data_cells[i].bytes.as_ptr(),pointers[i],"complete reference preserves original proof/public allocations");}')
s=s.replace('native and complete reference reach the same original first-call bytes','native and complete reference both succeed with the same first-call bytes')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('first-image-pair-v1','success-image-pair-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compilation then one paired accepted native/reference caller, exact native copy/implicit cleanup and selected checkpoint-byte equality. Existing entry normalization and tail leaf predecessor checks are green; no resource-cap raise.',remaining='Every assertion and both covers must pass. Instantiate necessary-image normalization and original scan/comparison/pure-child facts; derive successful actual first1768-byte class from source acceptance, use exact original-byte frame for proof/public and general valid runtime heap/ABI/allocator/oracle and cross-TX correspondence. No full S2 claim from a restricted fixture alone.'),indent=2)+'\n')
