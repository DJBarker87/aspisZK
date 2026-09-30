#!/usr/bin/env python3
"""One frozen changed-leaf replay using the pinned R120 dependency cache."""
import hashlib
import json
import sys
from pathlib import Path
here = Path(__file__).parent
manifest = json.loads((here / 'r121-release-manifest.json').read_text())
source_root = Path('/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a')
for record in manifest['targets']:
    path = source_root / (record['target'] + '.lean')
    assert hashlib.sha256(path.read_bytes()).hexdigest() == record['sha256']
    sys.argv.extend(['--target', record['target']])
source = (here / 'run_r121_lean.py').read_text()
exec(compile(source, str(here / 'run_r121_lean.py'), 'exec'))
