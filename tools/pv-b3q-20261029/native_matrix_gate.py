from pathlib import Path
import json,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029')
r=subprocess.run(json.loads((H/'native-command.json').read_text()))
if r.returncode:raise SystemExit(r.returncode)
raise SystemExit(subprocess.run([str(H/'matrix-native')]).returncode)
