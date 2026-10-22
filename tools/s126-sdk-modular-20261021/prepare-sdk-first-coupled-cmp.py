#!/usr/bin/env python3
"""First-entry pair with a shared688-byte comparison choice and exact arguments.
Both calls must read the same original proof allocation and every candidate
coordinate from the common typed encoder reply. Actual comparison semantics
come from the separately checked native-SDK gate/reference theorem; this cut
does not assert that arbitrary bytes compare equal. All other libc comparisons
retain their original body. Actual source/cut congruence still must compose.
"""
from pathlib import Path
import json,hashlib,sys,subprocess
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-first-coupling.py'),str(out)],check=True)
p=out/'src/lib.rs';s=p.read_text()
s=s.replace('candidate:[u8;688],k:usize','candidate:[u8;688],k:usize,different:bool')
s=s.replace('candidate:kani::any(),k:instruction[1] as usize','candidate:kani::any(),k:instruction[1] as usize,different:kani::any()')
needle='fn plan()->';a=s.index(needle)
s=s[:a]+'''static mut CMP_CALLS:GhostStorage<[u8;2]>=GhostStorage{value:[0;2],allocation_tag:0x51a6000000000001};
static mut CMP_INDEX:GhostStorage<usize>=GhostStorage{value:0,allocation_tag:0x51a6000000000002};
#[no_mangle] pub static mut s126_keep_coupled_cmp:Option<extern "C" fn(*const u8,*const u8,usize)->i32>=None;
#[no_mangle] pub extern "C" fn s126_coupled_cmp(a:*const u8,b:*const u8,n:usize)->i32 {
 assert_eq!(n,688);let phase=unsafe{PHASE.value};assert!(phase<2);
 assert_eq!(unsafe{CALLS.value[phase]},[1,1,1,0],"comparison follows decoder validator encoder");
 let root=unsafe{NATIVE_ROOT_PTRS.value[0]};
 assert!(a==root || b==root,"comparison selects the original proof allocation");
 let candidate=if a==root {b}else{a};let index=unsafe{CMP_INDEX.value};assert!(index<688);
 assert_eq!(unsafe{candidate.add(index).read()},plan().candidate[index],"both comparison candidates are the common typed encoder result at every coordinate");
 unsafe{CMP_CALLS.value[phase]+=1;}
 if plan().different {1}else{0}
}
'''+s[a:]
s=s.replace('assert!(observer.is_none());assert_eq!(k,plan().k);','assert!(observer.is_none());assert_eq!(unsafe{CMP_CALLS.value[phase]},1);assert_eq!(k,plan().k);')
s=s.replace('unsafe{core::ptr::addr_of_mut!(CALLS.value)},','unsafe{core::ptr::addr_of_mut!(CALLS.value)},\n unsafe{core::ptr::addr_of_mut!(CMP_CALLS.value)},')
needle=' unsafe{NATIVE_ROOT_PTRS.value=pointers;'
assert s.count(needle)==1
s=s.replace(needle,''' let cmp_index:usize=kani::any();kani::assume(cmp_index<688);
 unsafe{CMP_INDEX.value=cmp_index;CMP_CALLS.value=[0;2];s126_keep_coupled_cmp=Some(s126_coupled_cmp);}
'''+needle)
s=s.replace('assert_eq!(unsafe{CALLS.value[0]},unsafe{CALLS.value[1]},"native/reference child prefix, counts and order coincide");','''assert_eq!(unsafe{CALLS.value[0]},unsafe{CALLS.value[1]},"native/reference child prefix, counts and order coincide");
  assert_eq!(unsafe{CMP_CALLS.value[0]},unsafe{CMP_CALLS.value[1]},"comparison entry counts coincide");''')
s=s.replace('#[kani::unwind(700)]','#[kani::unwind(48)]')
p.write_text(s)
p=out/'Cargo.toml';p.write_text(p.read_text().replace('first-coupling-v1','first-coupling-v2'))
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,comparison_cut='Only C memcmp calls of length688 route to the retained extern-C Rust observer. It checks original proof pointer, exact candidate byte at arbitrary index0..687 and ordered child prefix for both phases; a common read-only Boolean choice determines0/nonzero. All other comparisons forward original memcmp. This is a relational cut; actual value semantics and source/cut transport remain required, not an assertion of prefix equality.')
p.write_text(json.dumps(m,indent=2)+'\n')
