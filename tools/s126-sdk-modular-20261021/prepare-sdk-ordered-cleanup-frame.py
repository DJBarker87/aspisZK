#!/usr/bin/env python3
"""One ordered post-copy cleanup step, full actual SDK/owner types.
No large copy/havoc occurs inside the checked function. Actual SDK acquisition
supplies guards, full actual statement and arbitrary1768-byte reply owners.
Checked raw guard and owner leaves execute in the exact source relative order;
only the three real borrow counters may be written. Explicit/implicit cleanup,
release deallocation dispatch/ABI/runtime mapping still need source transport.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-ordered-tail-raw.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();a=s.index('#[kani::requires(std::mem::size_of_val(&proof)');b=s.index('#[kani::proof] #[kani::unwind(48)]',a)
body='''#[kani::requires(std::mem::size_of_val(&proof)==2*std::mem::size_of::<usize>() && std::mem::size_of_val(&public)==2*std::mem::size_of::<usize>() && std::mem::size_of_val(&checkpoint)==2*std::mem::size_of::<usize>())]
#[kani::requires(unsafe{*(std::ptr::addr_of!(proof).cast::<usize>().add(1))}==counters[0] as usize)]
#[kani::requires(unsafe{*(std::ptr::addr_of!(public).cast::<usize>().add(1))}==counters[1] as usize)]
#[kani::requires(unsafe{*(std::ptr::addr_of!(checkpoint).cast::<usize>().add(1))}==counters[2] as usize)]
#[kani::requires(unsafe{(*counters[0]).get()}>0 && unsafe{(*counters[1]).get()}>0 && unsafe{(*counters[2]).get()} == -1)]
#[kani::requires(reply.len()==1768)]
#[kani::modifies(counters[0].cast_mut().cast::<isize>(),counters[1].cast_mut().cast::<isize>(),counters[2].cast_mut().cast::<isize>())]
#[kani::ensures(|_|unsafe{(*counters[0]).get()}==old(unsafe{(*counters[0]).get()})-1 && unsafe{(*counters[1]).get()}==old(unsafe{(*counters[1]).get()})-1 && unsafe{(*counters[2]).get()}==0)]
fn ordered_cleanup(proof:std::cell::Ref<'_,&mut[u8]>,public:std::cell::Ref<'_,&mut[u8]>,checkpoint:std::cell::RefMut<'_,&mut[u8]>,counters:[*const Cell<isize>;3],statement:Box<PoolV1PairForestTerminalStatementV1>,candidate:[u8;688],reply:Vec<u8>){
 let mut proof=std::mem::ManuallyDrop::new(proof);
 let mut public=std::mem::ManuallyDrop::new(public);
 let mut checkpoint=std::mem::ManuallyDrop::new(checkpoint);
 let mut statement=std::mem::ManuallyDrop::new(statement);
 let mut reply=std::mem::ManuallyDrop::new(reply);
 destroy_owner(std::ptr::null_mut(),&mut *reply,false);
 finish_guard_shared(&mut *proof,counters[0]);
 let _=candidate;
 destroy_owner(&mut *statement,std::ptr::null_mut(),true);
 finish_guard_shared(&mut *public,counters[1]);
 finish_guard_exclusive(&mut *checkpoint,counters[2]);
}
'''
s=s[:a]+body+s[b:]
s=s.replace('#[kani::proof] #[kani::unwind(48)]\n#[kani::stub_verified(encoded_finish)]', '#[kani::proof_for_contract(ordered_cleanup)] #[kani::unwind(48)]')
s=s.replace('fn actual_sdk_finish_drop_chain(){','fn actual_sdk_ordered_cleanup(){')
a=s.index(' let reply:[u8;1769]=kani::any();let reply_len:',s.index('fn actual_sdk_ordered_cleanup()'));b=s.index(' let actual:Result<(),ProgramError>=Ok(());',a)
s=s[:a]+''' let reply=kani::vec::exact_vec::<u8,1768>();
 ordered_cleanup(proof_data,public_data,checkpoint_data,counters,statement,candidate,reply);
'''+s[b:]
needle=' kani::cover!(initial_counts[0]==isize::MAX-1';a=s.index(needle,s.index('fn actual_sdk_ordered_cleanup()'))
s=s[:a]+s[a:].replace('"actual three guard Drops restore both maximum source counters"','"ordered owner and guard cleanup restores both maximum source counters"').replace('"actual three guard Drops restore both zero source counters"','"ordered owner and guard cleanup restores both zero source counters"')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('ordered-tail-links-raw-v2','ordered-cleanup-frame-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,order=['reply owner','proof guard','Copy candidate','statement owner','public guard','checkpoint guard'],expected_time='Cached optimized compilation then counter-only DFCC cleanup, no1768-byte copy/havoc and no proof/public indexed observation. The separately green copy and raw/owner leaves remain unchanged.',remaining='Every frame, safety, leaf precondition, restored-count assertion and source cover must pass. Match exact source/tool/ABI leaf pins; compose actual source copy footprint with this cleanup frame and its concrete counter/data separation. Explicit/compiler cleanup equivalence, release allocator/valid owner/runtime mapping, pure child/oracle/TX2 joins remain; not full S2.'),indent=2)+'\n')
