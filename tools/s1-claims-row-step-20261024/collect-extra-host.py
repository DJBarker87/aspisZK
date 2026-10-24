#!/usr/bin/env python3
from pathlib import Path
import json,shutil,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');N=H/'s1-claims-row-step-v1-20261024';M=H/'s1-claims-row-step-min-v1-20261024';X=H/'s1-claims-row-owned-extract-v1-20261024';P=N/'source-only-extra';P.mkdir(exist_ok=False)
for w,tag,attempt in [(N,'uninit-full','v7'),(M,'uninit-min','v8')]:
 d=P/tag;d.mkdir()
 shutil.copytree(w/'results'/('claims_row_write_preserves_initialized_prefix-'+attempt),d/'attempt')
 shutil.copyfile(w/('claims_row_write_preserves_initialized_prefix-'+attempt+'-admission.json'),d/'admission.json')
 for f in ['Cargo.toml','Cargo.lock','source-binding.json','proofs.rs','run-host.py','admit-host.py','HostAdmission.py','prepare-host.py']:shutil.copyfile(w/f,d/f)
 if tag=='uninit-min':shutil.copytree(w/'src',d/'src')
for phase in ['charon','aeneas']:
 shutil.copytree(X/phase,P/phase)
 shutil.copyfile(N/(phase+'-v1-admission.json'),P/(phase+'-admission.json'))
for f in ['binding.json','Cargo.toml','Cargo.lock']:shutil.copyfile(X/f,P/('extraction-'+f))
shutil.copyfile(X/'frozen-probe/src/r1_semantic.rs',P/'owned-reference.rs')
shutil.copytree(X/'generated',P/'generated')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();files={str(p.relative_to(P)):sha(p) for p in P.rglob('*') if p.is_file()}
assert not any(Path(n).suffix in ['.olean','.ir','.llbc','.rlib','.rmeta','.so','.o','.a','.pyc'] for n in files)
(P/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Both explicit uninit-checks probes are compiler ICEs before SAT, not proved memory results or counterexamples. Extraction/translation passes do not close native uninitializedness.'),indent=2)+'\n')
print(json.dumps(dict(files=len(files))))
