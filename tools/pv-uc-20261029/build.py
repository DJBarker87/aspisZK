from pathlib import Path
import subprocess,os,json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029'); C=H/'src/tools/r1-cost-probe'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'))
# Private target directory; the original harness and cache remain unchanged.
subprocess.run(['sh','./build-client.sh'],cwd=C,env=env,check=True)
p=Path(env['CARGO_TARGET_DIR'])/'client/user_client'
b=p.read_bytes();(H/'client-build.json').write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),recipe=(C/'build-client.sh').read_text()),indent=2)+'\n')
