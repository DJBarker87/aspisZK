#!/usr/bin/env python3
"""Concrete caller preconditions for the checked copy/Drop frame leaves.
Original SDK methods and actual std guards execute; no SDK model stubs. The
actual copy destination, all three guard counter words/live counts, and counter
regions outside every account data allocation are assertions. This links
already checked leaf frames without whole-caller DFCC or proof-byte muxing.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-tail.py'),str(O),'2'],check=True)
p=O/'src/lib.rs';s=p.read_text()
needle='  let mapped_reply=if first_ok';assert s.count(needle)==1
checks='''  assert_eq!(std::mem::size_of_val(&checkpoint_data),2*std::mem::size_of::<usize>());
  assert_eq!(std::mem::size_of_val(&public_data),2*std::mem::size_of::<usize>());
  assert_eq!(std::mem::size_of_val(&proof_data),2*std::mem::size_of::<usize>());
  assert_eq!(unsafe{*(std::ptr::addr_of!(checkpoint_data).cast::<usize>().add(1))},counters[2] as usize);
  assert_eq!(unsafe{*(std::ptr::addr_of!(public_data).cast::<usize>().add(1))},counters[1] as usize);
  assert_eq!(unsafe{*(std::ptr::addr_of!(proof_data).cast::<usize>().add(1))},counters[0] as usize);
  assert_eq!(checkpoint_data.as_mut_ptr(),pointers[2].cast_mut());
  assert_eq!(public_data.as_ptr(),pointers[1]);assert_eq!(proof_data.as_ptr(),pointers[0]);
  assert_eq!(unsafe{(*counters[2]).get()},-1);
  assert_eq!(unsafe{(*counters[1]).get()},initial_counts[1]+1);
  assert_eq!(unsafe{(*counters[0]).get()},initial_counts[0]+1);
  for c in 0..3 {for d in 0..3 {
   let counter=counters[c] as usize;let start=pointers[d] as usize;
   assert!(counter.checked_add(std::mem::size_of::<isize>()).is_some());
   assert!(start.checked_add(lengths[d]).is_some());
   assert!(counter+std::mem::size_of::<isize>()<=start || start+lengths[d]<=counter,
    "actual guard counter region is disjoint from every account data buffer");
  }}
'''
s=s.replace(needle,checks+needle)
needle='   let source=checkpoint.as_ptr().cast::<[u8;1768]>();';assert s.count(needle)==1
s=s.replace(needle,needle+'\n   assert_eq!(destination,pointers[2].cast_mut().cast::<[u8;1768]>(),"verified finish frame targets original checkpoint account2 allocation");')
needle='  // Exact relative guard/owner declaration order retained:';assert s.count(needle)==1
s=s.replace(needle,'''  assert_eq!(unsafe{(*counters[2]).get()},-1,"exclusive Drop precondition survives the exact native finish");
  assert!(unsafe{(*counters[1]).get()}>0 && unsafe{(*counters[0]).get()}>0,"both shared Drop preconditions survive finish");
'''+needle)
p.write_text(s)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s126-sdk-native-post-first-tail-root2-v5','aspis-s126-sdk-native-tail-leaf-links-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='All properties/source covers must pass. Then compose independently checked exact copy and actual Drop leaves using these actual caller preconditions/disjoint regions; owner deallocation/source scope, actual child/gate/scan/runtime/oracle/TX2 transport remain. Not a whole S2 closure.'),indent=2)+'\n')
