"""Supply frozen Rust include/path dependencies omitted by the initial narrow snapshot."""
from pathlib import Path
import json,re,subprocess,hashlib
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';base='/home/dombarker/project-offloads/codex-pv-cblib-20261027';host='dombarker@100.108.41.90';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
tracked=set(subprocess.check_output(['git','ls-files'],cwd=root,text=True).splitlines());known=set()
for name in ['candidate-snapshot.json','candidate-c3-snapshot.json']:
 known.update(json.loads((out/name).read_text())['files'])
todo=[root/p for p in known if p.endswith('.rs')];seen=set();added=set()
while todo:
 p=todo.pop()
 if p in seen:continue
 seen.add(p)
 for ref in re.findall(r'(?:#\[path\s*=\s*|include(?:_bytes|_str)?!\s*\(\s*)"([^"]+)"',p.read_text()):
  q=(p.parent/ref).resolve()
  if not q.is_relative_to(root):continue
  k=str(q.relative_to(root))
  if k in tracked and k not in known:
   added.add(k);known.add(k)
   if k.endswith('.rs'):todo.append(q)
# The tree module's path resolution is part of the cfg-kani native closure.
added.update(p for p in tracked if p.startswith('tools/r1-builder-reference/') and p.endswith('.rs') and p not in known)
paths=sorted(added)
r=subprocess.run(['ssh',host,f'python3 {gate}/reservation.py {base}/includes-upload.json > {base}/includes-upload.log 2>&1; cat {base}/includes-upload.log'],text=True,capture_output=True);(out/'includes-upload.log').write_text(r.stdout+r.stderr);assert r.returncode==0 and json.loads(r.stdout)['allowed']
a=subprocess.Popen(['git','archive','bd47052f039ae2d96060acb5607fe652ebe193d4',*paths],cwd=root,stdout=subprocess.PIPE);p=subprocess.run(['ssh',host,f'tar -x -C {base}/source'],stdin=a.stdout);a.stdout.close();assert a.wait()==0 and p.returncode==0
(out/'candidate-include-snapshot.json').write_text(json.dumps({'files':{p:{'sha256':hashlib.sha256((root/p).read_bytes()).hexdigest(),'size':(root/p).stat().st_size} for p in paths}},indent=2)+'\n')
print('added',len(paths),'frozen include inputs')
