import hashlib,json,sys
from pathlib import Path
H=Path(sys.argv[1]);f=json.loads((H/'candidate-source-hashes.json').read_text());r=[]
for n,s in f['files'].items():
 p=H/'src'/n; a=hashlib.sha256(p.read_bytes()).hexdigest();r.append(dict(path=n,expected=s,actual=a,equal=a==s))
assert all(x['equal'] for x in r),[x for x in r if not x['equal']]
(H/'source-validation.json').write_text(json.dumps(dict(task_revision='2318acd430b8474de01e6117248442e3ab0b17b9',frozen_source_revision=f['source_revision'],files=r,verifier_source_changes=False),indent=1)+'\n');print(len(r),'frozen source hashes match')
