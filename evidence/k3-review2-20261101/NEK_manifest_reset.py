"""Repair own scratch reset inventory to cover harness-only TOML overlays."""
from NEK_host import *
from NEK_scan import FROZEN,ROOT,sha
files={}
for n in subprocess.check_output(['git','ls-tree','-r','--name-only',FROZEN],text=True).splitlines():
 if n.endswith('.toml') and n.startswith(('crates/','programs/')):files[n]=subprocess.check_output(['git','show',FROZEN+':'+n]).decode()
admit('NEK_MANIFEST_RESET')
r=py(f'''from pathlib import Path
import json,zlib,base64,hashlib
b=Path({B!r});f=json.loads((b/'NEK_FROZEN_RS.json').read_text());add=json.loads(zlib.decompress(base64.b64decode({base64.b64encode(zlib.compress(json.dumps(files).encode())).decode()!r})));f.update(add);(b/'NEK_FROZEN_RS.json').write_text(json.dumps(f));print(json.dumps({{n:hashlib.sha256(t.encode()).hexdigest() for n,t in add.items()}}))
''');assert r.returncode==0,r.stderr;(E/'NEK_FROZEN_MANIFEST_RESET.json').write_text(r.stdout)
