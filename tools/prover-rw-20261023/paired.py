#!/usr/bin/env python3
"""Focused full-byte/L1/supplied-oracle paired differential, never a timing gate."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];H=R.parent
assert len(sys.argv)==7,'usage: paired.py label baseline-binary candidate-binary first count oracle-log'
label=sys.argv[1];B=dict(zip(['baseline','candidate'],map(Path,sys.argv[2:4])));first,count,log=sys.argv[4:7]
pins={k:dict(path=str(b),sha256=hashlib.sha256(b.read_bytes()).hexdigest(),bytes=b.stat().st_size) for k,b in B.items()}
(H/(label+'-binaries.json')).write_text(json.dumps(pins,indent=2)+'\n')
for kind in ['baseline','candidate']:
 subprocess.run([str(B[kind]),str(H/(label+'-'+kind)),first,count,log],check=True)
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/compare-corpus.py'),str(H/(label+'-baseline')),str(H/(label+'-candidate')),str(H/(label+'-comparison.json'))],check=True)
