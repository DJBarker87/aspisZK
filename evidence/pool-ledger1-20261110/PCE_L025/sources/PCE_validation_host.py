from pathlib import Path
import json,lzma,base64,hashlib,subprocess,os,shutil,sys
B=Path.cwd();D=B/'PCE_validation_data'/'evidence';files=json.loads((B/'PCE_VALIDATION_BUNDLE.json').read_text())
for rel,v in files.items():
 assert '..' not in Path(rel).parts and not Path(rel).is_absolute()
 raw=lzma.decompress(base64.b64decode(v['data']));assert hashlib.sha256(raw).hexdigest()==v['sha256']
 p=D/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
E=D/'pool-ledger1-20261110';r=subprocess.run(['python3',str(E/'PCE_VALIDATOR.py')],env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
if r.returncode==0:shutil.copyfile(E/'PCE_VALIDATION.json',B/'PCE_VALIDATION.json')
sys.exit(r.returncode)
