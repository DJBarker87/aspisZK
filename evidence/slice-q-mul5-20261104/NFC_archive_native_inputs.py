from pathlib import Path
import subprocess,json,base64,hashlib
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,lzma,base64,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul5-20261029');S=B/'NFC_src'
pins=json.loads((B/'NFC_SOURCE_PINS.json').read_text());files={}
for name,h in pins.items():
 p=S/name;data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==h,name
 files[name]=data.decode()
raw=json.dumps(dict(files=files,sha256=pins),sort_keys=True).encode();packed=lzma.compress(raw,preset=6)
print(json.dumps(dict(base64=base64.b64encode(packed).decode(),sha256=hashlib.sha256(raw).hexdigest(),compressed_sha256=hashlib.sha256(packed).hexdigest(),files=len(files),uncompressed_bytes=len(raw))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);data=base64.b64decode(x.pop('base64'));assert hashlib.sha256(data).hexdigest()==x['compressed_sha256']
(E/'NFC_NATIVE_INPUTS.json.xz').write_bytes(data);(E/'NFC_NATIVE_INPUTS.json.sha256').write_text(x['sha256']+'  NFC_NATIVE_INPUTS.json\n');(E/'NFC_NATIVE_INPUTS_MANIFEST.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
