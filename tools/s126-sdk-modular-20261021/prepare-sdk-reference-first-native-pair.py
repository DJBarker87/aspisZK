#!/usr/bin/env python3
"""Complete fixed-initial reference BEFORE actual native SDK execution.
Move original buffers into the complete owned reference, then recover its
proof/public vectors and restore ONLY checkpoint from a real initial clone.
The already proved complete reference input-buffer frames supply the native
initial-input identity; no post-native proof/public frame or58KiB clone is used.
Both complete bodies and native copy/implicit cleanup execute, no SDK models.
Pure child/scan/comparison ports and runtime/oracle/TX2 binding stay explicit.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-success-bytes-pair.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();a=s.index('  let model=OwnedSdk{');b=s.index('{',a)+1;depth=1
while depth:depth+=(s[b]=='{')-(s[b]=='}');b+=1
assert s[b]==';';b+=1;model=s[a:b];s=s[:a]+s[b:]
old='data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes:if i==2 {checkpoint_initial.take().unwrap()}else{bytes},borrowed:'
assert model.count(old)==1
model=model.replace(old,'data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:')
# Move the model metadata/counter assertions to immediately after its run,
# before moving its original proof/public vectors back to native inputs.
a=s.index('  for i in 0..3 {',s.index(' // Native handles are gone.'));b=s.index('\n }\n kani::cover!',a);checks=s[a:b]
checks=checks.replace('complete reference preserves original proof/public allocations','reference executed on the fixed original proof/public allocations')
a=s.index(' // Native handles are gone.');b=s.index(' kani::cover!',a)
s=s[:a]+''' if actual.is_ok() {
  assert!(expected.is_ok(),"native acceptance derives complete reference success on fixed initial inputs");
  assert_eq!(model_checkpoint_byte,plan().output[checkpoint_index],"fixed-initial reference and native save the same first checkpoint coordinate");
  assert_eq!(unsafe{CALLS.value[0]},unsafe{CALLS.value[1]},"same child prefix and order on native acceptance");
  assert_eq!(unsafe{CMP_CALLS.value[0]},unsafe{CMP_CALLS.value[1]},"same comparison count on native acceptance");
 }
'''+s[b:]
needle=' let mut checkpoint_initial=Some(buffers[2].clone());';assert s.count(needle)==1
s=s.replace(needle,''' let checkpoint_initial=buffers[2].clone();
'''+model+'''
 unsafe{PHASE.value=1;}
 let (expected,model)=owned::owned_stage1(program.to_bytes(),model,instruction[..instruction_len].to_vec());
'''+checks+'''
 let model_checkpoint_byte=model.data_cells[2].bytes[checkpoint_index];
 let [proof_cell,public_cell,checkpoint_cell]:[OwnedDataCell;3]=model.data_cells.try_into().ok().unwrap();
 let mut buffers=[proof_cell.bytes,public_cell.bytes,checkpoint_initial];
 let pointers=core::array::from_fn::<_,3,_>(|i|buffers[i].as_ptr());
 assert_eq!(pointers[0],unsafe{NATIVE_ROOT_PTRS.value[0]});assert_eq!(pointers[1],unsafe{NATIVE_ROOT_PTRS.value[1]});
 unsafe{NATIVE_ROOT_PTRS.value=pointers;PHASE.value=0;}
''')
assert s.index('owned::owned_stage1(')<s.index(' let actual={')
assert 'checkpoint_initial.take()' not in s and 'model_buffers' not in s
# Destruction of this detached old checkpoint is outside either checked caller.
s=s.replace(' let mut buffers=[proof_cell.bytes,public_cell.bytes,checkpoint_initial];',' drop(checkpoint_cell);\n let mut buffers=[proof_cell.bytes,public_cell.bytes,checkpoint_initial];')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('success-bytes-pair-v1','reference-first-native-pair-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compilation then complete reversed-order paired caller. Original58KiB buffers move without cloning; only original1768-byte CP is cloned/restored. Native copy and implicit cleanup execute; same8G cap.',remaining='Every assertion/cover must pass. Existing complete reference success/error buffer frames must identify recovered proof/public with original fixed inputs; original1768-byte clone identifies CP. Actual native accepted control completeness, pure child/scan/comparison meaning, first-entry argument bytes, runtime/ABI/allocator/oracle/TX2 and native output account frame remain. No whole S2.'),indent=2)+'\n')
