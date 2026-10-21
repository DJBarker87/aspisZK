#!/usr/bin/env python3
"""Generate/check the bounded extracted success-inversion proof."""
from pathlib import Path
import subprocess
import sys
here=Path(__file__).resolve().parent
root=here.parents[1]
target=root/'docs/research/100bit-spend-path-20261013/lean/OraclePortCkptAbiSourceFields.lean'
before=target.read_bytes() if target.exists() else None
for script in ['generate-source-fields.py','complete-source-fields.py']:
    subprocess.run([sys.executable,'-B',str(here/script)],check=True)
after=target.read_bytes()
if '--check' in sys.argv:
    if before != after:
        if before is not None:
            target.write_bytes(before)
        raise SystemExit('Generated source differs')
    print('Generated source matches')
