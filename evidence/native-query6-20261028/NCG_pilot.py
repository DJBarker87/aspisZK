from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
# Reuse the exact inherited fragment and input domain; change only own stub semantics.
ns={};exec((E.parent/'native-query5-20261028/NBZ_dots.py').read_text().replace('NBZ','NCG').replace("E=Path(__file__).resolve().parent","E=Path('/tmp')"),ns)
s=Path('/tmp/NCG_dots.rs').read_text()
s=s.replace('let out:u64=kani::any();kani::assume(out as u128==old as u128+(x as u128)*(y as u128));','let out:u64=kani::any(); // opaque whole add-product result: no value constraint')
# Only base pilot harnesses, inherited extra helpers are unreachable.
s=s[:s.index('#[kani::proof]')]+s[s.index('#[kani::proof]'):s.index('#[kani::proof]',s.index('fn NCG_base_gate_negative'))]
Path('/tmp/NCG_native.rs').write_text(s)
(E/'NCG_native.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
