#!/usr/bin/env python3
"""Native source first entry supplies the reference-constructor control facts.
One native execution, real SDK/guards/full statement and full original buffers.
The original scan is ghost-factored, evaluated once and its result recorded;
its iterator constructor is checked at the actual source site. The ordinary
read-only std-any and comparison abstractions stay unconstrained. Existing
exact source loop/gate laws, rather than new loop evaluation, must supply byte
zero/equality consequences. No complete reference execution is assumed.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-first-entry.py'),str(O),'2'],check=True)
p=O/'src/lib.rs';s=p.read_text();needle='fn plan()->';a=s.index(needle)
extra='''static mut CONSTRUCTOR_META_READY:GhostStorage<bool>=GhostStorage{value:false,allocation_tag:0x51aa000000000001};
static mut INITIAL_TAG:GhostStorage<u8>=GhostStorage{value:0,allocation_tag:0x51aa000000000002};
static mut SCAN_RESULT:GhostStorage<Option<bool>>=GhostStorage{value:None,allocation_tag:0x51aa000000000003};
pub fn scan_enter(iter:&std::slice::Iter<'_,u8>){
 let bytes=iter.as_slice();assert_eq!(bytes.len(),1768);
 assert_eq!(bytes.as_ptr(),unsafe{NATIVE_ROOT_PTRS.value[2]},"actual scan iterator starts at original checkpoint root2");
 assert_eq!(unsafe{(*COUNTERS.value[2]).get()},-1,"actual source scan holds exclusive checkpoint guard");
 assert_eq!(unsafe{CALLS.value[0]},[0,0,0,0],"scan precedes all decoder/validator/encoder/first calls");
 assert!(!std::mem::needs_drop::<std::slice::Iter<'_,u8>>(),"source iterator fission has no destructor effect");
 let index=unsafe{FRAME_INDEX.value};assert!(index<bytes.len());
 assert_eq!(bytes[index],unsafe{FRAME_BYTE.value},"actual native scan input is the original checkpoint byte at every coordinate");
}
pub fn scan_leave(hit:bool){unsafe{SCAN_RESULT.value=Some(hit);}}
'''
s=s[:a]+extra+s[a:]
original='checkpoint_data.iter().any(|byte| *byte != 0)';assert s.count(original)==1
replacement='''{
        let mut source_iter=checkpoint_data.iter();
        crate::proofs::scan_enter(&source_iter);
        let hit=source_iter.any(|byte| *byte != 0);
        crate::proofs::scan_leave(hit);
        hit
    }'''
s=s.replace(original,replacement)
needle=' // No candidate-coordinate claim in this unilateral read-only comparison overapproximation.';assert s.count(needle)==1
s=s.replace(needle,''' assert_eq!(unsafe{candidate.add(index).read()},plan().candidate[index],"native candidate coordinate is the actual common typed encoder result");''')
needle=' let input=unsafe{ENTRY_SCALARS.value.unwrap()};';assert s.count(needle)==1
s=s.replace(needle,needle+'''
 assert!(unsafe{CONSTRUCTOR_META_READY.value},"native first derives all original reference metadata/key/owner preconditions");
 assert_eq!(unsafe{SCAN_RESULT.value},Some(false),"native first implies actual source scan returned false");
 assert_eq!(unsafe{INITIAL_TAG.value},2,"native first derives original unmodified S2 tag image");
 assert!(!plan().different,"native first implies the source guard comparison returned equal");
''')
needle=' let cmp_index:usize=kani::any();kani::assume(cmp_index<688);';assert s.count(needle)==1
s=s.replace(needle,needle+'''
 unsafe{CONSTRUCTOR_META_READY.value=keys[0]!=keys[1] && keys[0]!=keys[2] && keys[1]!=keys[2]
  && !flags[0][0] && !flags[0][1] && !flags[0][2]
  && !flags[1][0] && !flags[1][1] && !flags[1][2]
  && owners[2]==program && !flags[2][0] && flags[2][1] && !flags[2][2];
  INITIAL_TAG.value=buffers[0][696];}
''')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('first-entry-root2-v2','constructor-ready-v4'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,scan_fission=dict(original=original,replacement=replacement,qualification='Let-introduction around exactly one native iterator/any call. Additional calls only read/check or update tagged ghost storage; iterator has no destructor. Explicit equivalence/noninterference is a required certificate gate, not silently assumed.'),remaining='All assertions and both covers must pass; instantiate existing concrete SDK iterator/std-any and exact prefix-gate laws at these checked native arguments. Construct the full reference execution from native-produced metadata/byte/child facts; actual child/oracle, continuation and runtime/TX2 transport remain. No whole S2.'),indent=2)+'\n')
