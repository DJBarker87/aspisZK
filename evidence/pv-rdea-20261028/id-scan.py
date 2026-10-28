from pathlib import Path
import os,re,json,datetime
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');base=D.parent
pattern=re.compile(r'(?:^|[-_])(603\d\d)(?:[-_.]|$)')
rows=[]
for job in base.glob('codex-pv-*'):
 if not job.is_dir():continue
 for root,dirs,files in os.walk(job):
  # Receipt scans exclude build caches and source corpora, never receipt roots.
  dirs[:]=[n for n in dirs if n not in ['target','client-target','objects','lean-objects','actual-objects','sources','actual-sources','source','src','node_modules','.git','.lake','native-source','repo']]
  for n in dirs+files:
   m=pattern.search(n)
   if m:rows.append(dict(id=int(m[1]),path=str(Path(root)/n),own_job=job==D))
G=base/'aspis-fs-generic-20261006/evidence'
for i in range(60300,60400):
 p=G/f'out-{i}.log'
 if p.exists():rows.append(dict(id=i,path=str(p),shared_output=True))
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),range=[60300,60399],matches=rows,other_job_matches=[r for r in rows if r.get('own_job') is False])
(D/'id-scan.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(scanned_range=r['range'],other_job_matches=r['other_job_matches'],shared_outputs=[r['id'] for r in rows if r.get('shared_output')])));assert not r['other_job_matches']
