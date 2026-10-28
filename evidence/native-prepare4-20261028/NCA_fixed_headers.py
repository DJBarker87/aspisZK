"""Split the dynamic empty-row fission into fixed five-byte source windows.
One local134-byte prefix carrier; actual full14759 native framing stays OPEN.
"""
from pathlib import Path
E=Path(__file__).resolve().parent
s='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
attrs='''#[kani::proof]#[kani::unwind(7)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
for row in [0,1]+list(range(3,14)):
 at=32+5*row if row<=2 else 64+5*row
 for wrong in [False,True]:
  s+=attrs+'fn NCA_header_fixed'+str(row)+('_wrong' if wrong else '')+'(){\n'
  s+=' let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();\n'
  if wrong:
   s+=f' let k:usize=kani::any();kani::assume(k<5);out[{at}..{at+5}].copy_from_slice(&input[{at}..{at+5}]);assert_ne!(out[{at}+k],input[{at}+k],"negative fixed header byte");\n'
  else:
   s+=f' let k:usize=kani::any();kani::assume(k<134);let old=out[k];out[{at}..{at+5}].copy_from_slice(&input[{at}..{at+5}]);assert_eq!(out[k],if k>={at}&&k<{at+5}{{input[k]}}else{{old}});kani::cover!(k=={at+4},"last reached header byte");\n'
  s+='}\n'
Path('/private/tmp/NCA_fixed_headers.rs').write_text(s)
# Exact standalone proposed harness patch, in addition to per-attempt applied patches.
import difflib
(E/'NCA_FIXED_HEADERS.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCA_candidate.rs')))
