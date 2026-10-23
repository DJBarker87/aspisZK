#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];H=R.parent;F=H.parent/'codex-cx-adapter-rw-20261023';rows=[]
for mode,filename in [('default','aspis_r1_cost_probe_program.so'),('devnet','aspis_r1_cost_probe_program.so'),('pool','aspis_pool.so')]:
    actual=H/'artifacts'/('proverw001-'+mode)/filename
    expected=F/('S2E-artifacts-'+mode)/filename
    a,b=actual.read_bytes(),expected.read_bytes()
    rows.append(dict(mode=mode,candidate=str(actual),retained=str(expected),bytes=len(a),sha256=hashlib.sha256(a).hexdigest(),retained_sha256=hashlib.sha256(b).hexdigest(),full_byte_identical=a==b))
result=dict(rows=rows,passed=all(r['full_byte_identical'] for r in rows),print_axioms='N/A: native binary full-byte comparison')
(H/'elf-byte-comparison.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));assert result['passed']
