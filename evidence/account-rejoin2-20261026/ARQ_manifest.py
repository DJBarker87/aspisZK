"""Read-only task provenance collector; no build or admission infrastructure."""
from pathlib import Path
import json,subprocess,shlex
P=Path(__file__).resolve().parent
remote="""
from pathlib import Path
import hashlib,json
B=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
files=list(B.glob('ARQ_*.lean'))+list(B.glob('ARQ_*.olean'))
files += [B/'Rc9_Top.lean',B/'Rc9_Top.olean',B/'S2W_lean_host.py',B/'S2W_run_host.py',Path('/home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py')]
out={p.name:dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in files if p.is_file()}
print(json.dumps(out,indent=2))
"""
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(remote)],capture_output=True,text=True,check=True)
(P/'ARQ_HOST_MANIFEST.json').write_text(r.stdout)
