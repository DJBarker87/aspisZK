from pathlib import Path
import sys,json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
names=[p.stem for p in E.glob('NBV_K[0-9][0-9][0-9].json') if (E/p.stem/'receipt.json').is_file()]+[p.stem for p in E.glob('NBV_L[0-9][0-9][0-9].json') if (E/p.stem/'receipt.json').is_file()]
r=h.remote_py(f'''from pathlib import Path
import json
b=Path({h.B!r});out={{}}
for a in {names!r}:
 for suffix in ['.json','-graph.json','-metadata.stderr']:
  p=b/(a+suffix)
  if p.is_file():out[p.name]=p.read_text()
 root=b/a/'sources'
 for p in root.rglob('*'):
  if p.is_file():out[str(p.relative_to(b))]=p.read_text()
print(json.dumps(out))''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
files=subprocess.check_output(['git','ls-tree','-r','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs','Cargo.toml','Cargo.lock'],text=True).splitlines()
out={}
for n in files:
 old=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n]);now=(R/n).read_bytes();assert old==now,n
 out[n]=dict(sha256=hashlib.sha256(now).hexdigest(),size=len(now))
(E/'NBV_FROZEN_SOURCE_PINS.json').write_text(json.dumps(out,indent=2)+'\n');print('frozen files byte-identical',len(out),'attempts',len(names))
