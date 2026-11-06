from pathlib import Path
import json,lzma,hashlib,subprocess,base64
b=Path(__file__).resolve().parent;s=b/'NJL_src';s.mkdir(exist_ok=True)
raw=lzma.decompress((b/'NJL_FROZEN_INPUTS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(b/'NJL_FROZEN_INPUTS.json.sha256').read_text().strip()
for n,text in json.loads(raw).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),str(p);p.write_bytes(base64.b64decode(text))
for patch in ['NJL_KMX.patch','NJL_native.patch']:
 subprocess.run(['git','apply','--check',str(b/patch)],cwd=s,check=True)
 subprocess.run(['git','apply',str(b/patch)],cwd=s,check=True)
print('Frozen scratch staged; exact KMX and cfg-only control module applied')
