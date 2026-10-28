"""Remove only key-free private compiled scratch after the checked stop."""
from pathlib import Path
import hashlib,json,shutil,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
modules=['PV_B2_RawWeights251Types','PV_B2_RawWeights253Types','PV_B2_RawWeights253Funs','PV_B2_ErrorBoundaryProbe','PV_B2_ErrorCounterexample']
objects=[]
for name in modules:
 p=H/'lean-objects/R1Z'/(name+'.olean');assert p.exists(),p
 objects.append(dict(module='R1Z/'+name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(H/'batch2b-output-object-pins.json').write_text(json.dumps(objects,indent=2)+'\n')
def keyshape(x):
 if isinstance(x,list):
  if len(x)==64 and all(type(a) is int and 0<=a<=255 for a in x):return True
  return any(keyshape(a) for a in x)
 if isinstance(x,dict):return any(keyshape(a) for a in x.values())
 return False
rows=[]
for name in ['charon-target','lean-objects']:
 p=H/name;assert p.parent==H;files=list(p.rglob('*')) if p.exists() else []
 suspect=[]
 for q in files:
  if q.is_symlink() or not q.is_file():continue
  if q.suffix in ['.key','.pem'] or q.name.endswith('keypair.json'):suspect.append(str(q));continue
  if q.suffix=='.json':
   try:
    if keyshape(json.loads(q.read_text())):suspect.append(str(q))
   except (ValueError,UnicodeError):pass
 row=dict(path=str(p),entries=len(files),suspected_key_paths=suspect)
 if suspect:row['action']='retained: potential key material; no cleanup'
 else:
  if p.exists():shutil.rmtree(p)
  row['action']='removed key-free private compiled scratch'
 rows.append(row)
keys=json.loads((H/'batch2b-key-retention.json').read_text())
assert all(Path(r['path']).exists() and (Path(r['path']).stat().st_mode&0o777)==0o600 for r in keys['keys'])
j=dict(epoch=time.time(),source_revision=(H/'candidate/source-revision.txt').read_text().strip(),paths=rows,object_pins='OUTPUT-OBJECT-PINS.json',keys='all18 task/SBF keys remain mode0600; no transaction/refund/key cleanup',shared_caches='untouched; reused SBF/native caches were not removed',print_axioms='N/A: file hygiene; no build')
(H/'batch2b-cache-cleanup.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
