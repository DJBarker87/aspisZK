"""Source/static-data gate; optimized native compilation is the expected cost."""
from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
for name in ['v260-project-source.py','v260-constants.py']:
 subprocess.run(['python3',str(D/name)],check=True)
results={name:hashlib.sha256((D/name).read_bytes()).hexdigest() for name in ['range-source-result.json','v260-word-source-result.json','v260-project-source-result.json','v260-constants-result.json']}
(D/'v260-gate-result.json').write_text(json.dumps(dict(results=results,scope='Source patterns, concrete uint bindings and full static data only; full Lean row proofs and concrete library disposition still required',composition='Reclassification within existing tool trust; zero endpoint premise removal'),indent=2)+'\n')
print('V260 source/static-data checks passed; no whole-row credit from this gate alone')
