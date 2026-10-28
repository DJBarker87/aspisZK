from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
m=json.loads((H/'source-batch3c-repair.json').read_text());bad=[]
for n,h in m['files'].items():
 p=H/'source'/n
 a=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
 if a!=h:bad.append(dict(path=n,expected=h,actual=a))
out=dict(revision=m['revision'],files_checked=len(m['files']),mismatches=bad,binaries={n:hashlib.sha256((H/'bin'/n).read_bytes()).hexdigest() for n in ['batch3b-split-counterexample','batch3c-split-counterexample']})
(H/'batch3c-source-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
