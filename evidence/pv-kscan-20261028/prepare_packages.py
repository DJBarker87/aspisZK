from pathlib import Path
import shutil,re,json,hashlib
R=Path('/home/dombarker/project-offloads/codex-pv-kscan-20261028')
plans={'K06':'/home/dombarker/project-offloads/codex-pv-cb3-20261026/kani-proof','K07':'/home/dombarker/project-offloads/codex-pv-cb-20261026/proof','K08':'/home/dombarker/project-offloads/codex-pv-dlib-20261028/native-proof','K09':'/home/dombarker/project-offloads/codex-cx-batch-effects3-20261026/repo/evidence/batch-effects3-20261026/BEg_native','K10':'/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/NP6_claims'}
for run,src in plans.items():
 src=Path(src);dst=R/run/'package';dst.mkdir(parents=True,exist_ok=True);records=[]
 for p in src.rglob('*'):
  if not p.is_file() or any(x in p.relative_to(src).parts for x in ['target','.git']):continue
  if not (p.suffix=='.rs' or p.name in ['Cargo.toml','Cargo.lock']):continue
  q=dst/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True);b=p.read_bytes();s=b.decode()
  if p.name=='Cargo.toml' or p.suffix=='.rs':
   s=re.sub(r'(path\s*=\s*")([^"\n]+)(")',lambda m:m[1]+str((p.parent/m[2]).resolve())+m[3] if m[2].startswith('../') else m[0],s)
  q.write_text(s);records.append(dict(source=str(p),destination=str(q),source_sha256=hashlib.sha256(b).hexdigest(),relocated_sha256=hashlib.sha256(s.encode()).hexdigest()))
 (R/run/'source-relocations.json').write_text(json.dumps(records,indent=2)+'\n')
 print(run,len(records))
