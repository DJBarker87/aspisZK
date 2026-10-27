"""Record scratch-only harnesses as a reviewable patch; no shipped writes."""
from pathlib import Path
import difflib
E=Path(__file__).resolve().parent;root='crates/aspis-r1-cost-probe/src/';parts=[]
for f,new in [('lib.rs',Path(root+'lib.rs').read_text()+'\n#[cfg(kani)] mod LPe_replay;\n'),('fast_pairing.rs',Path('/tmp/LPe_fast_pairing.rs').read_text()),('verifier.rs',Path('/tmp/LPe_native_verifier.rs').read_text())]:
 old=Path(root+f).read_text();parts.append(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+root+f,tofile='b/'+root+f)))
for f in ['LPe_replay.rs','LPe_verifier.rs']:
 parts.append(''.join(difflib.unified_diff([],Path('/tmp',f).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+root+f)))
(E/'LPe_harness.patch').write_text(''.join(parts))
