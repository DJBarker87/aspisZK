from pathlib import Path
import json,hashlib,subprocess,base64
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownl-20261029';D='/home/dombarker/project-offloads/codex-pv-ownl-20261029'
# Entire original statement crate, not rewritten/sliced copies of the roots.
paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD','crates/aspis-statement','crates/aspis-core','crates/aspis-prover'],text=True).splitlines()
records=[]
for rel in paths:
 b=subprocess.check_output(['git','show','HEAD:'+rel]);records.append(dict(path=rel,sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(E/'crate-source-pins.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),files=records),indent=2)+'\n')
code='from pathlib import Path\nimport base64,json,hashlib\nD=Path('+repr(D)+');D.mkdir(exist_ok=True)\n'
code+='pins='+repr(records)+'\nF=Path("/home/dombarker/project-offloads/codex-pv-fscan-20261028/src")\n'
code+='for p in pins:\n b=(F/p["path"]).read_bytes();assert len(b)==p["size"] and hashlib.sha256(b).hexdigest()==p["sha256"],p["path"]\n'
for name in ['harness.rs','native.py']:
 b=(R/'tools/pv-ownl-20261029'/name).read_bytes();code+='(D/'+repr(name)+').write_bytes(base64.b64decode('+repr(base64.b64encode(b).decode())+'))\n'
b=(E/'crate-source-pins.json').read_bytes();code+='(D/"crate-source-pins.json").write_bytes(base64.b64decode('+repr(base64.b64encode(b).decode())+'))\n'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
print('identical full statement crate:',len(records),'files; prepared source inputs only')
