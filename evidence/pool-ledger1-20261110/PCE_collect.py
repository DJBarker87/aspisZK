"""Collect only own raw graphs and scan; preserve original-byte SHA256."""
from pathlib import Path
import json,subprocess,lzma,base64,hashlib
E=Path(__file__).resolve().parent
code="""from pathlib import Path
import json,base64,lzma,hashlib
B=Path('/home/dombarker/project-offloads/codex-pc-pool-ledger1-20261110');out=[]
for p in list(B.glob('PCE_NEP_*'))+[B/'PCE_LOADED_scan.jsonl']:
 if p.is_file():
  raw=p.read_bytes();out.append(dict(name=p.name,sha256=hashlib.sha256(raw).hexdigest(),data=base64.b64encode(lzma.compress(raw,preset=6)).decode()))
print(json.dumps(out))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
xs=json.loads(r.stdout)
for x in xs:
 raw=lzma.decompress(base64.b64decode(x['data']));assert hashlib.sha256(raw).hexdigest()==x['sha256']
 (E/(x['name']+'.xz')).write_bytes(base64.b64decode(x['data']));(E/(x['name']+'.sha256')).write_text(x['sha256']+'\n')
print('Collected '+str(len(xs))+' own compressed graphs/scan with original-byte hashes.')
