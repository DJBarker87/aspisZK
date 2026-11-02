from pathlib import Path
import json,lzma,base64,sys
root=Path('/home/dombarker/project-offloads/codex-pv-k3scan-20261101')
p=root/sys.argv[1];assert not p.exists();p.mkdir()
for n,b in json.loads(lzma.decompress((root/sys.argv[2]).read_bytes())).items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=p/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(base64.b64decode(b))
