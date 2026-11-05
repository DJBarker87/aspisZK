"""Replace huge by-value arbitrary input construction with direct local havoc.
No source function, assertion, logical domain or resource limit is weakened.
"""
from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent;p=E/'NHF_WIDE_BYTE_TEMPLATE.rs.txt';s=p.read_text()
s=s.replace('let proof:[u8;57607]=kani::any();','''let mut storage=Box::<[u8;57607]>::new_uninit();
 unsafe{kani::internal::write_any(kani::internal::Pointer::assignable(storage.as_mut_ptr()));}
 let proof=unsafe{storage.assume_init()};''').replace('cut(&proof,&semantic,&y1,&mut log)','cut(&proof[..],&semantic,&y1,&mut log)')
p.write_text(s)
s=s.replace('NHF_BYTE_VALUE','0');(E/'NHF_wide.rs.txt').write_text(s)
pins=json.loads((E/'NHF_SOURCE_PINS.json').read_text());pins['crates/aspis-r1-cost-probe/src/NHF_wide.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NHF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
p=E/'NHF_native.patch';patch=p.read_text();a=patch.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NHF_wide.rs\n');p.write_text(patch[:a]+''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NHF_wide.rs')))
