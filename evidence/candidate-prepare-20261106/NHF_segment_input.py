"""Represent the SAME fully arbitrary57607 bytes in three contiguous u8 fields.
No sparse/zero fixture: every header, decoder and suffix byte is arbitrary.
The layout assertions and Lean take/drop theorem expose the representation.
"""
from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent
s=(E/'NHF_K013/sources/NHF_src/crates/aspis-r1-cost-probe/src/NHF_wide.rs').read_text()
pos=s.index('struct DecodeLog')
s=s[:pos]+'''#[repr(C)]
struct ProofBacking{header:[u8;7495],inactive:[u8;32],suffix:[u8;50080]}
'''+s[pos:]
s=s.replace('let proof:[u8;57607]=kani::any();','''let backing=ProofBacking{header:kani::any(),inactive:kani::any(),suffix:kani::any()};
 assert_eq!(core::mem::size_of::<ProofBacking>(),57607);
 assert_eq!(core::mem::align_of::<ProofBacking>(),1);
 assert_eq!(core::mem::offset_of!(ProofBacking,inactive),7495);
 assert_eq!(core::mem::offset_of!(ProofBacking,suffix),7527);
 let proof=unsafe{core::slice::from_raw_parts((&backing as *const ProofBacking).cast::<u8>(),57607)};
 assert_eq!(proof.as_ptr() as usize+7495,backing.inactive.as_ptr() as usize);''')
s=s.replace('cut(&proof,&semantic,&y1,&mut log)','cut(proof,&semantic,&y1,&mut log)')
(E/'NHF_wide.rs.txt').write_text(s)
pins=json.loads((E/'NHF_SOURCE_PINS.json').read_text());pins['crates/aspis-r1-cost-probe/src/NHF_wide.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NHF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
p=E/'NHF_native.patch';patch=p.read_text();a=patch.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NHF_wide.rs\n');p.write_text(patch[:a]+''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NHF_wide.rs')))
