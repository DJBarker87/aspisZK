from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
s=E/'extraction/inactive-owner/AspisR1InactiveOwner49/Funs.lean'
t=s.read_text();start=t.index('/-- [simulator_inactive_owner49::owned::MASKS]');end=t.index('end AspisR1InactiveOwner49',start)
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitInactiveSource49.lean')
p.write_text('import Aeneas\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnamespace AspisR1InactiveOwner49\n\n'+t[start:end]+'end AspisR1InactiveOwner49\n')
(E/'pins/inactive-extraction-binding.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),selection='All owned declarations, exact extracted bodies, no arithmetic rewrite'),indent=2)+'\n')
