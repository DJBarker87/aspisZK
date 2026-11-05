from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent;patch=''
for n in ['crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/weights.rs']:
 old=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
 new=('#![cfg_attr(kani,feature(allocator_api))]\n'+old) if n.endswith('/lib.rs') else old+'\n#[cfg(kani)] #[path="NIT_tail.rs"] mod NIT_tail;\n'
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
n='crates/aspis-r1-cost-probe/src/NIT_tail.rs';patch+=''.join(difflib.unified_diff([], (E/'NIT_tail.rs.txt').read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+n))
(E/'NIT_gap_cuts.patch').write_text(patch)
