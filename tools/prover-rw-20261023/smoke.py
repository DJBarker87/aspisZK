#!/usr/bin/env python3
"""Ten whole-pipeline pairs with exact oracle streams and L1 records."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];H=R.parent
pins={}
for kind in ['baseline','candidate']:
    b=H/'native-artifacts'/('corpus-'+kind+'-001')
    pins[kind]=dict(sha256=hashlib.sha256(b.read_bytes()).hexdigest(),bytes=b.stat().st_size)
(H/'smoke-binaries.json').write_text(json.dumps(pins,indent=2)+'\n')
for kind in ['baseline','candidate']:
    subprocess.run([str(H/'native-artifacts'/('corpus-'+kind+'-001')),str(H/('smoke-'+kind+'-001')),'0','10','1'],check=True)
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/compare-corpus.py'),str(H/'smoke-baseline-001'),str(H/'smoke-candidate-001'),str(H/'smoke-comparison.json')],check=True)
