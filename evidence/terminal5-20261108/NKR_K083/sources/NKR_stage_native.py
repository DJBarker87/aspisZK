from pathlib import Path
import json,lzma,hashlib,subprocess,base64
b=Path(__file__).resolve().parent;s=b/'NKR_src';s.mkdir(exist_ok=True)
raw=lzma.decompress((b/'NKR_FROZEN_INPUTS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(b/'NKR_FROZEN_INPUTS.json.sha256').read_text().strip()
for n,text in json.loads(raw).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);data=base64.b64decode(text)
 if p.exists():assert p.read_bytes()==data,str(p)
 else:p.write_bytes(data)
for patch in ['NKR_KMX.patch','NKR_native.patch']:
 subprocess.run(['git','apply','--check',str(b/patch)],cwd=s,check=True)
 subprocess.run(['git','apply',str(b/patch)],cwd=s,check=True)
print('Frozen scratch staged with exact KMX and NKR cfg-only module')
