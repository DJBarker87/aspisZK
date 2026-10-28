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

# Pinned inputs and complete job-owned project dependency closure at capture time.
for cohort,S,O in [('physical',D.parent/'aspis-joint-20261019/sources',D.parent/'aspis-joint-20261019/objects'),('actual',D/'actual-sources',D/'actual-objects')]:
 roots=list((S/'R1Z').glob('PV_RDEA_*.lean'));seen={};pending=[('R1Z.'+x.stem) for x in roots]
 while pending:
  m=pending.pop()
  if m in seen:continue
  p=S/(m.replace('.','/')+'.lean');o=O/(m.replace('.','/')+'.olean')
  if not p.exists():continue
  raw=p.read_bytes();imports=[]
  for line in raw.decode().splitlines():
   if line.startswith('import '):imports.extend(line[7:].split())
  seen[m]=dict(module=m,source=str(p),source_sha256=hashlib.sha256(raw).hexdigest(),object=str(o),object_sha256=hashlib.sha256(o.read_bytes()).hexdigest() if o.exists() else None,imports=imports)
  pending.extend(x for x in imports if x.startswith('R1Z.'))
 (D/f'{cohort}-closure-final.json').write_text(json.dumps(list(seen.values()),indent=2)+'\n')
