from pathlib import Path
import json,subprocess,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029')
x=json.loads((H/'charon.json').read_text())
for p,h in [('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/charon','daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'),('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2','fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68')]:
 assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h
r=subprocess.run(x['command'],cwd=x['cwd']);sys.exit(r.returncode)
