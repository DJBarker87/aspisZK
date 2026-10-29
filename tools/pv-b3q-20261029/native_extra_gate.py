from pathlib import Path
import subprocess,json,sys
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029');cmd=json.loads((H/(sys.argv[1]+'-command.json')).read_text());r=subprocess.run(cmd['compile'])
if r.returncode:raise SystemExit(r.returncode)
raise SystemExit(subprocess.run(cmd['run']).returncode)
