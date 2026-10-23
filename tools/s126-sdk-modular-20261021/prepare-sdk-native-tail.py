#!/usr/bin/env python3
"""Exact post-first source tail in actual SDK guard/owner context.
Native-entry certificates supply canonical slots and admissible live counts.
The independently checked full-ProgramError native_finish contract is reused.
Every reply length0..1769 and the actual mapped first-error image is included.
No SDK carrier/model replacement; full actual statement Box type retained.
"""
from pathlib import Path
import json,hashlib,subprocess,sys,re
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);root=int(sys.argv[2]);assert root in [0,1,2] and not O.exists()
window=int(sys.argv[3]) if len(sys.argv)>3 else None
if window is not None:assert root==0 and 0<=window<15
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-first-entry.py'),str(O),'2'],check=True)
p=O/'src/lib.rs';base=p.read_text();prefix=base[:base.index('#[cfg(kani)] mod proofs')]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-parent-cuts/sources'
leaf=(E/'sdk-finish-fixed-frame-v5/src/lib.rs').read_text();a=leaf.index('fn native_finish(');b=leaf.index('#[cfg(kani)] mod proofs',a);helper=leaf[a:b]
leaf_harness=leaf[b:].replace('mod proofs {','mod copy_certificate {',1)
a=base.index('fn statement()->');b=base.index('fn planned_scan',a);statement=base[a:b]
a=base.index('fn native_owned_decoder_prefix(){');main=base[a:base.rfind('\n}')]
main=main.replace('fn native_owned_decoder_prefix(){','fn native_post_first_tail(){',1)
main=main.replace(' let selected_root:usize=2;',f' let selected_root:usize={root};')
if window is not None:main=main.replace(' let selected_index:usize=kani::any();kani::assume(selected_index<buffers[selected_root].len());',f' let offset:u16=kani::any();let selected_index:usize={4096}*{window}+(offset%4096) as usize;kani::assume(selected_index<buffers[selected_root].len());')
main=main.replace(' unsafe{FRAME_ROOT.value=selected_root;FRAME_INDEX.value=selected_index;FRAME_BYTE.value=buffers[selected_root][selected_index];}',' let initial_byte=buffers[selected_root][selected_index];')
main=main.replace(' let data_slots:[usize;3]=kani::any();',' let data_slots:[usize;3]=[0,1,2];')
needle=' let initial_counts:[isize;3]=kani::any();let initial_lamport_counts:[isize;3]=kani::any();'
assert main.count(needle)==1
main=main.replace(needle,needle+'''
 kani::assume(initial_counts[2]==0);
 for i in 0..2 {kani::assume(initial_counts[i]>=0 && initial_counts[i]<isize::MAX);}
''')
a=main.index(' let cmp_index:usize=');b=main.index(' let actual={',a)
main=main[:a]+''' let reply:[u8;1769]=kani::any();let reply_len:usize=kani::any();kani::assume(reply_len<=1769);let first_ok:bool=kani::any();
'''+main[b:]
main=main.replace(' unsafe{COUNTERS.value=counters;}\n','')
a=main.index(' let actual=native_prefix(');b=main.index(' for i in 0..3 {\n  assert_eq!(unsafe{(*counters[i]).get()}',a)
main=main[:a]+''' let actual={
  let mut checkpoint_data=accounts[2].try_borrow_mut_data().unwrap();
  let public_data=accounts[1].try_borrow_data().unwrap();
  let statement=Box::new(statement());
  let candidate:[u8;688]=kani::any();
  let proof_data=accounts[0].try_borrow_data().unwrap();
  let mapped_reply=if first_ok {Ok(reply[..reply_len].to_vec())}else{Err(ProgramError::InvalidInstructionData)};
  let result=(||{
   let checkpoint=mapped_reply?;
   let observed=if selected_root==2 {selected_index}else{0};
   let destination=checkpoint_data.as_mut_ptr().cast::<[u8;1768]>();
   let source=checkpoint.as_ptr().cast::<[u8;1768]>();
   let expected=if checkpoint.len()==1768 {checkpoint[observed]}else{checkpoint_data[observed]};
   let ok=encoded_finish(&mut checkpoint_data,&checkpoint,observed,destination,source,expected);
   if ok {Ok(())} else {Err(ProgramError::InvalidAccountData)}
  })();
  // Exact relative guard/owner declaration order retained: reply, proof,
  // candidate, actual statement Box, public guard, checkpoint guard.
  let _=(&proof_data,&candidate,&statement,&public_data);
  result
 };
'''+main[b:]
a=main.index(' // Native handles are gone.');main=main[:a]+''' for i in 0..3 {
 assert!(keys[i]==keys[i]); // Input keys/owners are shared immutable borrows.
 }
 if first_ok && reply_len==1768 {
  assert!(actual.is_ok());
  if selected_root==2 {assert_eq!(buffers[2][selected_index],reply[selected_index]);}
  else {assert_eq!(buffers[selected_root][selected_index],initial_byte);}
 } else {
  if first_ok {assert!(matches!(actual,Err(ProgramError::InvalidAccountData)));}
  else {assert!(matches!(actual,Err(ProgramError::InvalidInstructionData)));}
  assert_eq!(buffers[selected_root][selected_index],initial_byte);
 }
 kani::cover!(actual.is_ok()&&selected_root==2&&initial_counts[0]==isize::MAX-1,"native tail saved byte and restored maximum proof borrow count");
 kani::cover!(first_ok&&reply_len!=1768&&matches!(actual,Err(ProgramError::InvalidAccountData)),"native tail exact length error");
 kani::cover!(!first_ok&&matches!(actual,Err(ProgramError::InvalidInstructionData)),"native tail exact mapped first error");
}
'''
# No vacuous metadata assertion is treated as evidence.
main=main.replace('actual.is_ok()&&selected_root==2&&','actual.is_ok()&&selected_root=='+str(root)+'&&')
main=main.replace(' for i in 0..3 {\n assert!(keys[i]==keys[i]); // Input keys/owners are shared immutable borrows.\n }\n','')
s=prefix+helper+leaf_harness+'#[cfg(kani)] mod proofs {\nuse super::*;use std::cell::Cell;\n'+statement+'#[kani::proof] #[kani::unwind(1772)]\n#[kani::stub_verified(encoded_finish)]\n'+main+'}\n'
p.write_text(s)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s126-sdk-shared-prefix-first-entry-root2-v2',(f'aspis-s126-sdk-native-post-first-tail-root{root}-window{window}-v6' if window is not None else f'aspis-s126-sdk-native-post-first-tail-root{root}-v5')))
sha=lambda b:hashlib.sha256(b).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(s.encode()),helper_sha256=sha(helper.encode()),helper_owner_source_sha256=sha(leaf.encode()),qualification=__doc__,observer_root=root,observer_window=window,derived_input_facts='Canonical original data slots[0,1,2], cp initial borrow0, proof/public initial counts nonnegative below isizeMAX. These are conclusions of corrected actual-SDK first-entry cases, not honest-run inputs. Full nonzero Rc headers and independent lamport aliases/counters retained.',return_encoding='Exact original native_finish body/full ProgramError retained; checked encoded_finish returns true for Ok, false for InvalidAccountData, panics on every other image (proved unreachable in retained v5 owner); caller reconstructs original full result. No custom Arbitrary/SDK type replacement.',remaining='Verify all properties/covers; instantiate exact old finish certificate at matching helper/ABI/ghost arguments, then compose entry with this actual SDK post-first chunk. Source child/gate/scan/complete caller/runtime/oracle/TX2 transport remains. Not a whole-stage proof or whole S2.'),indent=2)+'\n')
