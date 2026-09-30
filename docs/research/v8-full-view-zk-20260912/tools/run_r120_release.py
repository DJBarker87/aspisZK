#!/usr/bin/env python3
"""One frozen changed-manifest replay after all focused leaves are green."""
import hashlib,json,sys
from pathlib import Path
here=Path(__file__).parent
m=json.loads((here/'r120-release-manifest.json').read_text())
src=Path('/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a')
for r in m['targets']:
    assert hashlib.sha256((src/(r['target']+'.lean')).read_bytes()).hexdigest()==r['sha256']
    sys.argv.extend(['--target',r['target']])
source=(here/'run_r119_lean.py').read_text()
exec(compile(source,str(here/'run_r119_lean.py'),'exec'))
