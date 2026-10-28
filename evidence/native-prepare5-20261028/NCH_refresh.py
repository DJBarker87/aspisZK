from pathlib import Path
import difflib
p=Path('/private/tmp/NCH_candidate.rs');e=Path(__file__).resolve().parent
(e/'NCH_harness.patch').write_text(''.join(difflib.unified_diff([],p.read_text().splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCH_candidate.rs')))
