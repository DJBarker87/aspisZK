from pathlib import Path
import json
from RPt_attempt import E,B,T,ssh
paths=[T+'/bin/lean',T+'/bin/lake',B+'/S2W_run_host.py',B+'/lean-toolchain',B+'/lakefile.toml','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/Aeneas/Std/Core/Fmt.olean']
payload='''from pathlib import Path
import hashlib,json
paths=json.loads(%r)
paths += [str(p) for p in Path(paths[0]).parent.parent.joinpath('lib/lean').glob('*.so')]
print(json.dumps([{'path':n,'resolved_path':str(Path(n).resolve()),'sha256':hashlib.sha256(Path(n).read_bytes()).hexdigest(),'bytes':Path(n).stat().st_size} for n in paths]))
'''%json.dumps(paths)
r=ssh('python3 -',payload);assert r.returncode==0,r.stderr
(E/'RPt_toolchain-pins.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n');print(r.stdout)
