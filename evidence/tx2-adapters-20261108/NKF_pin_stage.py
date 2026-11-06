from NKF_formal import *
import base64
raw=lzma.decompress((E.parent/'ledger17-20261108/NKC_CLOSURE_PINS.json.xz').read_bytes())
assert sha(raw)==(E.parent/'ledger17-20261108/NKC_CLOSURE_PINS.json.sha256').read_text().strip()
rc=run('NKF_L035','pin','NKF_pin',['python3','NKF_pin.py'],{'NKF_pin.py':(E/'NKF_pin.py').read_text(),'NKF_PREDECESSOR_PINS.json':raw.decode()})
r=ssh('python3',f"from pathlib import Path;import json,base64;b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode()for n in ['NKF_CLOSURE_PINS.json.xz','NKF_CLOSURE_PINS.json.sha256','NKF_PREDECESSOR_COMPARISON.json','NKF_EXPORT.json','NKF_TOOL_PINS.json'] if (b/n).exists()}}))")
assert r.returncode==0
for n,t in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(t))
assert rc['exit_status']==0
