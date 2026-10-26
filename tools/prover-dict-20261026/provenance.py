"""Read-only tool and proof-input pins omitted by the inherited runner's old directory list."""
from pathlib import Path
import hashlib,json,subprocess
h=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026');r=h/'src';sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest();files=[]
paths=[Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release')/n for n in ['charon','charon-driver']]
paths+=[Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')]
paths+=[Path('/home/dombarker/.kani/kani-0.67.0/bin')/n for n in ['kani-driver','kani-compiler','cbmc','goto-instrument','kissat']]
paths+=list((r/'tools/prover-dict-20261026/proof-options').glob('*'))
for p in paths:
 if p.is_file():files.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
llbcs=[p for p in r.glob('PDict_*.llbc') if p.is_file()]+list((r/'tools/prover-dict-20261026/proof-options').glob('*.llbc'))
for p in llbcs:files.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
(h/'receipts/tool-and-proof-inputs.json').write_text(json.dumps(dict(files=files,print_axioms='N/A: read-only provenance; binary hashes/sizes only, no binary content exported',charon_version=subprocess.run([str(paths[0]),'version'],capture_output=True,text=True).stdout,charon_toolchain=subprocess.run([str(paths[0]),'toolchain-version'],capture_output=True,text=True).stdout),indent=2)+'\n');print(len(files))
