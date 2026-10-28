from KNB_host import *
import sys,zlib,base64
name=sys.argv[1]
admit('KNB_UPLOAD_'+name)
s=base64.b64encode(zlib.compress((E/('KNB_variant_'+name+'.rs.txt')).read_bytes())).decode()
r=py('from pathlib import Path\nimport base64,zlib\np=Path('+repr(B+'/KNB_src/crates/aspis-r1-cost-probe/src/NBZ_native.rs')+')\np.write_bytes(zlib.decompress(base64.b64decode('+repr(s)+')))');assert r.returncode==0,r.stderr
