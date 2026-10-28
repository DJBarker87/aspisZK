from pathlib import Path
import shutil,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');G=D.parent/'aspis-fs-generic-20261006/evidence';rows=[]
for i in range(60300,60400):
 for stem,ext in [('out','log'),('time','log'),('sha','txt')]:
  p=G/f'{stem}-{i}.{ext}';q=D/p.name
  if p.exists():
   if q.exists():assert p.read_bytes()==q.read_bytes(),(p,q)
   else:shutil.copyfile(p,q)
 p=D/f'out-{i}.log'
 if p.exists():rows.append(i)
(D/'used-ids.json').write_text(json.dumps(dict(ids=rows,count=len(rows)),indent=2)+'\n')
# Full object hashes for project declarations actually present in the two prefixes.
for group,p in [('physical',D.parent/'aspis-joint-20261019/objects/R1Z'),('actual',D/'actual-objects/R1Z')]:
 out=[]
 for f in sorted(p.glob('PV_RDEA_*.olean')):
  out.append(dict(module='R1Z.'+f.stem,path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
 (D/f'{group}-objects-final.json').write_text(json.dumps(out,indent=2)+'\n')
print('used IDs',len(rows),rows)
