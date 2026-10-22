#!/usr/bin/env python3
"""Actual SDK post-first chunk write-set proof: no symbolic proof-byte lookup.
The original SDK guards, exact finish body/full error image, actual statement
Box type and guard declaration/Drop order are retained. The verified finish
callee writes only checkpoint data. This checks the remaining write footprint
and restored counters rather than reducing a58295-byte observation mux.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-tail.py'),str(O),'2'],check=True)
p=O/'src/lib.rs';s=p.read_text();a=s.index(' let actual={\n  let mut checkpoint_data=');b=s.index('\n for i in 0..3 {\n  assert_eq!(unsafe{(*counters[i]).get()}',a);block=s[a:b]
block=block.replace(' let actual={','',1);assert block.endswith('\n };');block=block[:-4]
block=block.replace('let statement=Box::new(statement());','let statement=Box::new(statement_value);').replace('  let candidate:[u8;688]=kani::any();\n','')
block=block.replace('let observed=if selected_root==2 {selected_index}else{0};','let observed=0;')
block=block.replace('let destination=checkpoint_data.as_mut_ptr().cast::<[u8;1768]>();','assert_eq!(destination,checkpoint_data.as_mut_ptr().cast::<[u8;1768]>());')
fn='''#[kani::requires(reply_len<=1769)]
#[kani::requires(unsafe{(*counters[2]).get()}==0)]
#[kani::requires((0..2).all(|i|unsafe{(*counters[i]).get()}>=0 && unsafe{(*counters[i]).get()}<isize::MAX))]
#[kani::requires((0..3).all(|i|counters[i]==std::rc::Rc::as_ptr(&accounts[i].data).cast::<Cell<isize>>()))]
#[kani::requires(destination==unsafe{(&**accounts[2].data.as_ptr()).as_ptr()}.cast_mut().cast::<[u8;1768]>())]
#[kani::requires(unsafe{(&**accounts[2].data.as_ptr()).len()}==1768)]
#[kani::modifies(destination,counters[0].cast_mut().cast::<isize>(),counters[1].cast_mut().cast::<isize>(),counters[2].cast_mut().cast::<isize>())]
#[kani::ensures(|_|unsafe{(*counters[0]).get()}==old(unsafe{(*counters[0]).get()}) && unsafe{(*counters[1]).get()}==old(unsafe{(*counters[1]).get()}) && unsafe{(*counters[2]).get()}==old(unsafe{(*counters[2]).get()}))]
fn native_tail_frame(statement_value:PoolV1PairForestTerminalStatementV1,candidate:[u8;688],accounts:&[AccountInfo<'_>;3],reply:&[u8;1769],reply_len:usize,first_ok:bool,destination:*mut[u8;1768],counters:[*const Cell<isize>;3])->Result<(),ProgramError>{
'''+block+'''\n}\n'''
# The point fixture now invokes the exact chunk as a frame contract.
s=s[:a]+''' let statement_value=statement();let candidate:[u8;688]=kani::any();
 let actual=native_tail_frame(statement_value,candidate,&accounts,&reply,reply_len,first_ok,destination,counters);'''+s[b:]
a=s.index(' if first_ok && reply_len==1768 {',s.index('fn native_post_first_tail'));b=s.index(' kani::cover!(',a);s=s[:a]+s[b:]
s=s.replace(' let initial_byte=buffers[selected_root][selected_index];',' let destination=buffers[2].as_mut_ptr().cast::<[u8;1768]>();')
s=s.replace(' let selected_index:usize=kani::any();kani::assume(selected_index<buffers[selected_root].len());','')
s=s.replace('#[kani::proof] #[kani::unwind(1772)]','#[kani::proof_for_contract(native_tail_frame)] #[kani::unwind(1772)]',1)
s=s.replace('fn native_post_first_tail(){','fn native_tail_write_frame(){',1)
needle='#[kani::proof_for_contract(native_tail_frame)]';pos=s.index(needle);s=s[:pos]+fn+'\n'+s[pos:]
p.write_text(s)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s126-sdk-native-post-first-tail-root2-v5','aspis-s126-sdk-native-tail-write-frame-v4'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,write_set='Only actual checkpoint1768-byte destination and three actual SDK data borrow counters. Every counter restored; no data-byte observations or proof/public buffer reads are introduced by fixture.',remaining='All frame/caller/safety properties and source covers must pass. Need old finish-certificate/source/ABI instantiation, entry/post-first chunk composition, actual pure child/gate/scan and runtime/oracle/TX2 transport. Not a whole-stage execution proof.'),indent=2)+'\n')
