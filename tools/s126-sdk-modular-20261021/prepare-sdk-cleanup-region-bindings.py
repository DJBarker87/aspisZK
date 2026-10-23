#!/usr/bin/env python3
"""Concrete SDK regions for the checked copy/cleanup footprint composition.
No parent DFCC replay: the exact checked cleanup body/contract/leaf bodies stay
unchanged. Ordinary assertions bind its counters, original data views and
protected account metadata to disjoint actual ranges in the same full native
SDK/owner fixture. The source/domain/tool pins must match the direct frame.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-ordered-cleanup-direct-frame.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();original=s
s=s.replace('#[kani::proof_for_contract(ordered_cleanup)] #[kani::unwind(48)]','#[kani::proof] #[kani::unwind(48)]')
capture=' let [ref mut l0,ref mut l1,ref mut l2]=amounts;';assert s.count(capture)==1
s=s.replace(capture,' let original_amounts=amounts.as_mut_ptr();\n'+capture)
needle=' ordered_cleanup(proof_data,public_data,checkpoint_data,counters,statement,candidate,reply);';assert s.count(needle)==1
checks=''' let word=std::mem::size_of::<usize>();assert_eq!(word,8);assert_eq!(std::mem::size_of::<isize>(),8);
 assert_eq!(checkpoint_data.as_ptr(),pointers[2]);assert_eq!(checkpoint_data.len(),1768);
 assert_eq!(proof_data.as_ptr(),pointers[0]);assert_eq!(proof_data.len(),58295);
 assert_eq!(public_data.as_ptr(),pointers[1]);assert_eq!(public_data.len(),1880);
 for c in 0..3 {for d in 0..3 {
  regions_separate(counters[c] as usize,8,pointers[d] as usize,lengths[d]);
 }}
 regions_separate(pointers[2] as usize,1768,pointers[0] as usize,58295);
 regions_separate(pointers[2] as usize,1768,pointers[1] as usize,1880);
 for d in 0..3 {
  let data_base=std::rc::Rc::as_ptr(&accounts[d].data) as usize;
  let lamports_base=std::rc::Rc::as_ptr(&accounts[d].lamports) as usize;
  assert!(data_base>=2*word && lamports_base>=2*word);
  let protected=[
   (accounts[d].data.as_ptr() as usize,std::mem::size_of::<&mut[u8]>()),
   (data_base-2*word,2*word),
   (lamports_base-2*word,2*word+std::mem::size_of::<std::cell::RefCell<&mut u64>>()),
   (unsafe{original_amounts.add(d)} as usize,std::mem::size_of::<u64>()),
   (accounts[d].key as *const Pubkey as usize,std::mem::size_of::<Pubkey>()),
   (accounts[d].owner as *const Pubkey as usize,std::mem::size_of::<Pubkey>()),
   (std::ptr::addr_of!(accounts[d]) as usize,std::mem::size_of::<AccountInfo<'_>>()),
  ];
  for (base,len) in protected {
   regions_separate(pointers[2] as usize,1768,base,len);
   for c in 0..3 {regions_separate(counters[c] as usize,8,base,len);}
  }
 }
'''
s=s.replace(needle,checks+needle)
needle='#[kani::proof] #[kani::unwind(48)]';a=s.index(needle)
s=s[:a]+'''fn regions_separate(a:usize,na:usize,b:usize,nb:usize){
 assert!(a.checked_add(na).is_some());assert!(b.checked_add(nb).is_some());
 assert!(a+na<=b || b+nb<=a,"actual SDK protected region is outside copy/counter footprint");
}
'''+s[a:]
a=original.index('fn ordered_cleanup(');b=original.index('#[kani::proof_for_contract(ordered_cleanup)]',a);assert original[a:b] in s
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('ordered-cleanup-direct-frame-v1','cleanup-region-bindings-v2'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),unchanged_cleanup_sha256=hashlib.sha256(original[a:b].encode()).hexdigest(),qualification=__doc__,protected='All three data views; all three descriptors, data Rc headers, entire lamport Rc objects/headers, amounts, keys/owners and AccountInfo containers. Checkpoint copy is allowed to touch its data view only. Only actual data borrow flags are cleanup-writable.',remaining='All safety/separation/caller assertions and covers must pass. Retain exact old frame/copy/owner/SDK source/tool/host-ABI domain; supply source cleanup/fission and runtime mapping plus actual first/child/oracle/TX2 transport. No whole S2.'),indent=2)+'\n')
