from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;m=json.loads((E/'NHH_FROZEN_SCAFFOLD.json').read_text());es=m['files'];data=subprocess.check_output(['git','cat-file','--batch'],input=''.join(e['git_blob']+'\n'for e in es).encode());off=0;rows={}
for e in es:
 end=data.index(b'\n',off);head=data[off:end].decode().split();size=int(head[2]);body=data[end+1:end+1+size];off=end+size+2
 assert head[0]==e['git_blob']and head[1]=='blob'
 rows[e['path']]=hashlib.sha256(body).hexdigest()
(E/'NHH_FROZEN_RELEASE_PINS.json').write_text(json.dumps(dict(revision=m['revision'],files=rows,source='immutable git objects, not another live worktree',allowed_overrides=['crates/aspis-r1-cost-probe/src/lib.rs']),indent=1)+'\n')
print(json.dumps(dict(files=len(rows),sha256=hashlib.sha256((E/'NHH_FROZEN_RELEASE_PINS.json').read_bytes()).hexdigest())))
