#!/usr/bin/env python3
"""Actual typed SDK guard Drop sequence with a combined counter-only frame.
All original SDK acquisitions run in the harness. Actual std destructors run
inside checked helper; no SDK/Drop models or verified stubs. Full statement
Box/candidate destructors remain outside this guard-only subclaim.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-tail.py'),str(O),'2'],check=True)
p=O/'src/lib.rs';s=p.read_text();a=s.index(' let actual={\n  let mut checkpoint_data=');b=s.index('\n for i in 0..3 {\n  assert_eq!(unsafe{(*counters[i]).get()}',a)
s=s[:a]+''' let checkpoint_data=accounts[2].try_borrow_mut_data().unwrap();
 let public_data=accounts[1].try_borrow_data().unwrap();
 let proof_data=accounts[0].try_borrow_data().unwrap();
 native_drop_chain(proof_data,public_data,checkpoint_data,counters);
 let actual:Result<(),ProgramError>=Ok(());
'''+s[b:]
a=s.index(' if first_ok && reply_len==1768 {',s.index('fn native_post_first_tail'));s=s[:a]+''' kani::cover!(initial_counts[0]==isize::MAX-1 && initial_counts[1]==isize::MAX-1,"actual three guard Drops restore both maximum source counters");
 kani::cover!(initial_counts[0]==0 && initial_counts[1]==0,"actual three guard Drops restore both zero source counters");
}\n}\n'''
s=s.replace(' let initial_byte=buffers[selected_root][selected_index];','').replace(' let selected_index:usize=kani::any();kani::assume(selected_index<buffers[selected_root].len());','')
s=s.replace(' let reply:[u8;1769]=kani::any();let reply_len:usize=kani::any();kani::assume(reply_len<=1769);let first_ok:bool=kani::any();','')
s=s.replace('#[kani::proof] #[kani::unwind(1772)]\n#[kani::stub_verified(encoded_finish)]','#[kani::proof_for_contract(native_drop_chain)] #[kani::unwind(33)]',1).replace('fn native_post_first_tail(){','fn actual_sdk_drop_chain(){')
fn='''#[kani::requires(std::mem::size_of_val(&proof)==2*std::mem::size_of::<usize>() && std::mem::size_of_val(&public)==2*std::mem::size_of::<usize>() && std::mem::size_of_val(&checkpoint)==2*std::mem::size_of::<usize>())]
#[kani::requires(unsafe{*(std::ptr::addr_of!(proof).cast::<usize>().add(1))}==counters[0] as usize)]
#[kani::requires(unsafe{*(std::ptr::addr_of!(public).cast::<usize>().add(1))}==counters[1] as usize)]
#[kani::requires(unsafe{*(std::ptr::addr_of!(checkpoint).cast::<usize>().add(1))}==counters[2] as usize)]
#[kani::requires(unsafe{(*counters[0]).get()}>0 && unsafe{(*counters[1]).get()}>0 && unsafe{(*counters[2]).get()} == -1)]
#[kani::modifies(counters[0].cast_mut().cast::<isize>(),counters[1].cast_mut().cast::<isize>(),counters[2].cast_mut().cast::<isize>())]
#[kani::ensures(|_|unsafe{(*counters[0]).get()}==old(unsafe{(*counters[0]).get()})-1 && unsafe{(*counters[1]).get()}==old(unsafe{(*counters[1]).get()})-1 && unsafe{(*counters[2]).get()}==0)]
fn native_drop_chain(proof:std::cell::Ref<'_,&mut[u8]>,public:std::cell::Ref<'_,&mut[u8]>,checkpoint:std::cell::RefMut<'_,&mut[u8]>,counters:[*const Cell<isize>;3]){
 drop(proof);drop(public);drop(checkpoint);
}
'''
needle='#[kani::proof_for_contract(native_drop_chain)]';s=s.replace(needle,fn+'\n'+needle,1);p.write_text(s)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s126-sdk-native-post-first-tail-root2-v5','aspis-s126-sdk-native-drop-chain-v3'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='Verify combined frame and instantiate native leaf-links preconditions; statement/Vec owner effects, whole source execution, actual child/gate/scan/runtime/oracle/TX2 transport remain.'),indent=2)+'\n')
