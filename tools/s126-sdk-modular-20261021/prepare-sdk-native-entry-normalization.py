#!/usr/bin/env python3
"""Unseeded native stage1 entry derives canonical data slots at verifier entry.
The actual SDK body and all full Rc/borrow/metadata input domains are retained.
A common successful verifier child returns an empty Vec, so checkpoint write is
unreachable and no accepted-result or independently canonical-slot premise is used.
"""
from pathlib import Path
import sys,json,hashlib
base,out=map(Path,sys.argv[1:3]);(out/'src').mkdir(parents=True,exist_ok=False)
original=(base/'src/lib.rs').read_text();source=original
assert 'b0[696]=2' not in source
source=source.replace(' let output_len=1768usize;',' let output_len=0usize;')
source=source.replace('let data_slots:[usize;3]=[0,1,2];','let data_slots:[usize;3]=kani::any();')
a='accounts[i].lamports=lamport_roots[lamport_slots[i]].clone();'
assert source.count(a)==1;source=source.replace(a,'accounts[i].data=data_roots[data_slots[i]].clone();'+a)
a=' for i in 0..3 {assert!(std::rc::Rc::ptr_eq(&accounts[i].data,&data_roots[i]));assert_eq!(std::rc::Rc::strong_count(&data_roots[i]),2); }\n'
assert source.count(a)==1;source=source.replace(a,'')
a=source.index(' if actual.is_ok() {');b=source.index(' for i in 0..3 {\n  assert_eq!(unsafe{(*counters[i])',a)
source=source[:a]+''' assert!(actual.is_err(),"empty successful verifier reply rejects before checkpoint write");
 if unsafe{CALLS.value[0][3]}==1 {
  assert_eq!(data_slots,[0,1,2],"actual unseeded SDK verifier entry derives canonical data slots");
  for event in 0..4 {assert_eq!(unsafe{CALLS.value[0][event]},1);}
 }
'''+source[b:]
a=source.index(' kani::cover!(actual.is_ok(),');b=source.index('\n}\n}',a)
source=source[:a]+''' kani::cover!(unsafe{CALLS.value[0][3]}==1,"unseeded all-alias SDK state reaches exact first call");
 kani::cover!(unsafe{CALLS.value[0][3]}==1&&rc_counts[0][0]==usize::MAX,"source slot normalization supports full Rc domain");
 kani::cover!(unsafe{CALLS.value[0][3]}==1&&lamport_slots[0]==lamport_slots[1],"independent lamport alias retained at verifier entry");'''+source[b:]
assert source[:source.index('fn native_parent_arguments()')]==original[:original.index('fn native_parent_arguments()')]
prefix_cut='prefix-entry-cut' in sys.argv[3:]
if prefix_cut:
 source=source.replace('fn native_parent_arguments() {','''fn native_parent_arguments() {
 #[no_mangle] static mut s126_prefix_hits:usize=0x51a5000000000001;
 unsafe{s126_prefix_hits=0;}
''',1)
 source=source.replace(' if unsafe{CALLS.value[0][3]}==1 {',' if unsafe{s126_prefix_hits}>0 {',1)
 source=source.replace('  for event in 0..4 {assert_eq!(unsafe{CALLS.value[0][event]},1);}','  assert_eq!(unsafe{s126_prefix_hits},1);\n  for event in 0..3 {assert_eq!(unsafe{CALLS.value[0][event]},1);}')
 source=source.replace('actual unseeded SDK verifier entry derives canonical data slots','actual unseeded SDK prefix-comparison entry derives canonical data slots')
 source=source.replace('unsafe{CALLS.value[0][3]}==1','unsafe{s126_prefix_hits}==1')
 source=source.replace('exact first call','exact proof-prefix comparison entry')
first_link='first-link' in sys.argv[3:]
if first_link:
 assert prefix_cut
 source=source.replace(' if unsafe{s126_prefix_hits}>0 {',''' if unsafe{CALLS.value[0][3]}==1 {
  assert_eq!(unsafe{s126_prefix_hits},1,"actual verifier entry follows the original prefix-comparison entry");
  assert_eq!(data_slots,[0,1,2],"actual unseeded all-alias verifier entry derives canonical data slots");
  for event in 0..4 {assert_eq!(unsafe{CALLS.value[0][event]},1);}
 }
 if unsafe{s126_prefix_hits}>0 {''',1)
 source=source.replace('kani::cover!(unsafe{s126_prefix_hits}==1,','kani::cover!(unsafe{CALLS.value[0][3]}==1,')
 source=source.replace('kani::cover!(unsafe{s126_prefix_hits}==1&&','kani::cover!(unsafe{CALLS.value[0][3]}==1&&')
havoc_inputs='havoc-inputs' in sys.argv[3:]
if havoc_inputs:
 assert first_link
 before=' let mut b0:[u8;58295]=kani::any();let mut b1:[u8;1880]=kani::any();let mut b2:[u8;1768]=kani::any();'
 after=""" #[inline(never)] fn s126_input_bytes(p:*mut u8,n:usize)->usize {let _=(p,n);panic!("input initialization must be linked before verification")}
 let mut b0=Box::<[u8;58295]>::new_uninit();
 let mut b1=Box::<[u8;1880]>::new_uninit();
 let mut b2=Box::<[u8;1768]>::new_uninit();
 unsafe{s126_input_bytes(b0.as_mut_ptr().cast(),58295);s126_input_bytes(b1.as_mut_ptr().cast(),1880);s126_input_bytes(b2.as_mut_ptr().cast(),1768);}
 let mut b0=unsafe{b0.assume_init()};let mut b1=unsafe{b1.assume_init()};let mut b2=unsafe{b2.assume_init()};"""
 assert source.count(before)==1;source=source.replace(before,after)
 for i in range(3):source=source.replace('&mut b'+str(i)+',&owners','&mut b'+str(i)+'[..],&owners')
(out/'src/lib.rs').write_text(source);(out/'Cargo.toml').write_bytes((base/'Cargo.toml').read_bytes())
sha=lambda b:hashlib.sha256(b).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(source.encode()),base_source_sha256=sha(original.encode()),unchanged_source_and_helpers_sha256=sha(source[:source.index('fn native_parent_arguments()')].encode()),qualification=__doc__,domain='All unseeded proof/public/checkpoint bytes58295/1880/1768, independent arbitrary data/lamport slot maps0..2, all metadata, every signed borrow counter and nonzero usize Rc header. Actual unchanged source reaching its first_decoded/verifier child must derive data_slots=[0,1,2]; every returned path preserves the prior scalar/Rc postconditions. Common successful typed pure children remain explicit and exact first-call pointer/public/k/None assertions remain. The verifier returns a successful empty Vec; source length rejection must prevent every destination-copy invocation.',retained='Fixed rooted buffer lengths and concrete heap-construction domain; actual pure child instances, general runtime embedding, earlier source-prefix/scan transport and ordered state/log/oracle correspondence. This is source entry normalization, not a whole successful stage1 or S2 closure.'),indent=2)+'\n')
if prefix_cut:
 p=out/'source-cut.json';m=json.loads(p.read_text());m['entry_cut']='Only688-byte memcmp calls are marked and forced to return nonzero; all other lengths forward to the original libc model. The caller asserts canonical slots at the comparison entry, before any returned byte-comparison result is needed. The marker uses a no_mangle usize static with a nonzero initializer and is reset in the harness; no native source buffer/SDK behavior before the cut changes. Full first/observer/writeback correctness is not claimed from this entry cut.';p.write_text(json.dumps(m,indent=2)+'\n')
if first_link:
 p=out/'source-cut.json';m=json.loads(p.read_text());m['first_entry_link']='The comparison cut returns an arbitrary read-only i32 result, so both comparison outcomes and the original tag/first continuations execute. Native first/verifier entry must have exactly one prior prefix-comparison marker, canonical data slots and the same original typed public/proof/k/None arguments. This is universal in the comparison reply, not an assumed equality or actual comparison/body equivalence.';p.write_text(json.dumps(m,indent=2)+'\n')

if havoc_inputs:
 p=out/'source-cut.json';m=json.loads(p.read_text());m['input_constructor']='Harness-only Box<MaybeUninit<[u8;N]>> allocations, filled by linked CBMC __CPROVER_havoc_slice before assume_init, then ordinary typed SDK byte slices. All bytes remain arbitrary, no zeroing or equality premise. This changes rooted heap construction, not frozen native body or its helpers. CBMC intrinsic initialization semantics and exact C implementation are explicit tool trust.';p.write_text(json.dumps(m,indent=2)+'\n')
