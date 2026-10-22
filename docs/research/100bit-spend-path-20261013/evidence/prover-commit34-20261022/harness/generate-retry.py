#!/usr/bin/env python3
"""Retain the full native retry caller verbatim, substituting only callees/types."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
source=Path('crates/aspis-r1-cost-probe/src/prover.rs').read_text()
start=source.index('pub fn prove_masked_retrying_with(')
left=source.index('{',start);i=left+1;depth=1
while depth:depth+=(source[i]=='{')-(source[i]=='}');i+=1
body=source[start:i]
(H/'native-retry.rs').write_text('// Verbatim shipped function; type/callee substitutes are in lib.rs.\n'+body+'\n')
(H.parent/'retry-source-pins.json').write_text(json.dumps(dict(source_path='crates/aspis-r1-cost-probe/src/prover.rs',function='prove_masked_retrying_with',sha256=hashlib.sha256(body.encode()).hexdigest(),verbatim=True),indent=2)+'\n')
