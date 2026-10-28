from KNH_host import *
import base64,zlib
admit('KNH_K2UPLOAD')
files={p.name:p.read_text() for p in E.glob('KNH_k2_*.rs.txt')}
files['KNH_loops.rs.txt']=(E/'KNH_loops.rs.txt').read_text()
packed=base64.b64encode(zlib.compress(json.dumps(files).encode())).decode()
r=py('from pathlib import Path;import base64,zlib,json;b=Path('+repr(B)+');files=json.loads(zlib.decompress(base64.b64decode('+repr(packed)+')));[(b/n).write_text(v) for n,v in files.items()]');assert r.returncode==0
(E/'KNH_K2UPLOAD.json').write_text(json.dumps({n:hashlib.sha256(v.encode()).hexdigest() for n,v in files.items()},indent=2)+'\n')
