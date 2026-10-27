from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-quiet-20261027')
records=json.loads((H/'source-manifest.json').read_text());errors=[]
for side,rows in records.items():
 for path,pin in rows.items():
  file=H/side/'source'/path
  if not file.exists():errors.append([side,path,'missing'])
  elif hashlib.sha256(file.read_bytes()).hexdigest()!=pin['sha256']:errors.append([side,path,'mismatch'])
(H/'source-verification.json').write_text(json.dumps(dict(files={k:len(v) for k,v in records.items()},errors=errors,passed=not errors),indent=2)+'\n')
assert not errors,errors
