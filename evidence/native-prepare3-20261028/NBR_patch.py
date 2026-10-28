"""Retain exactly the own scratch cfg-module patch for the next native gate."""
from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent
p='crates/aspis-r1-cost-probe/src/candidate.rs'
s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
new=s+'\n#[cfg(kani)]\nmod NBR_candidate;\n'
h=Path('/private/tmp/NBR_candidate.rs').read_text()
patch=''.join(difflib.unified_diff(s.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+=''.join(difflib.unified_diff([],h.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBR_candidate.rs'))
(E/'NBR_harness.patch').write_text(patch)
