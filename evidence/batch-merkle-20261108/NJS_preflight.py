from pathlib import Path
import shutil,hashlib,json,subprocess
B=Path.cwd();src=Path('/home/dombarker/project-offloads/codex-cx-extract-stage-20261106');out=[]
for n in ['NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256','NHR_STAGING_MANIFEST.json']:
 p=src/n;q=B/n;shutil.copy2(p,q);out.append(dict(source=str(p),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
(B/'NJS_PINNED_INPUTS.json').write_text(json.dumps(out,indent=2)+'\n')
r=subprocess.run(['python3','NJS_NHR_stage.py','--check','--out','NJS_preflight']);raise SystemExit(r.returncode)
