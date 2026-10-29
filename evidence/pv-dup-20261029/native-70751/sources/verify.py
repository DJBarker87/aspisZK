from pathlib import Path
import json,hashlib,time,re
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.file_digest(Path(p).open('rb'),'sha256').hexdigest()
p=Path('/home/dombarker/project-offloads/codex-pv-evhc2-20261029/resume3/COHORT-MANIFEST.json');assert sha(p)=='f8ff7cfcc649f1b99a01b0703353d4856a472ac198884cb80b706863b9d07d65'
m=json.load(open(p));roots=list(map(Path,m['LEAN_PATH'].split(':')));start=time.monotonic();count=0
for e in m['entries']:
 top=e['module'].split('.')[0];r=next(r for r in roots if (r/top).is_dir() or (r/(top+'.olean')).is_file());assert r/(e['module'].replace('.','/')+'.olean')==Path(e['path'])
 for f in [e]+e['companions']:
  assert sha(f['path'])==f['sha256'],f['path'];count+=1
used=[]
for job in B.parent.iterdir():
 if job.is_dir():
  for sub in ['', 'evidence','receipts','resume3','resume4']:
   q=job/sub
   if not q.is_dir():continue
   it=q.iterdir() if sub=='' else q.rglob('*')
   for x in it:
    if re.search(r'(?<!\d)707(?:[5-8]\d|9[0-6])(?!\d)',x.name):used.append(str(x))
(B/'verified.json').write_text(json.dumps({'status':'PASS','modules':len(m['entries']),'files':count,'wall_seconds':time.monotonic()-start,'LEAN_PATH':m['LEAN_PATH'],'id_audit':used,'source_revision':'4318dfa7971c50aae74845a1488433d13f631385'},indent=2)+'\n')
print('PASS',len(m['entries']),count,flush=True)
