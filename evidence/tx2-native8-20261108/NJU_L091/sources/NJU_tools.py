"""Copy/pin retained tools into own workspace; no infrastructure is changed."""
from pathlib import Path
import shutil,hashlib,json
B=Path(__file__).resolve().parent;P=B.parent/'codex-cx-tx2-native7-20261108'
rows=[]
for name in ['S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 src=P/name;dst=B/name
 if dst.exists():assert dst.read_bytes()==src.read_bytes()
 else:shutil.copy2(src,dst)
 rows.append(dict(source=str(src),destination=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest(),bytes=dst.stat().st_size))
(B/'NJU_native').mkdir(exist_ok=True)
(B/'NJU_TOOL_PINS.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(pinned=len(rows),infrastructure_modified=False)))
