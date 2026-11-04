from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent;p=json.load(open(E/'PLAN.json'));rows=[];trees={}
for m,v in p['sources'].items():
 rev=v['revision'];matches=[]
 if re.fullmatch('[0-9a-f]{40}',rev):
  if not v['path'].startswith('/'):
   candidates=[v['path']]
  else:
   if rev not in trees:trees[rev]=subprocess.check_output(['git','ls-tree','-r','--name-only',rev],text=True).splitlines()
   candidates=[f for f in trees[rev] if f.startswith('evidence/pv-bridge-20261101/') and f.endswith('/'+m+'.lean')]
  for f in candidates:
   r=subprocess.run(['git','show',rev+':'+f],capture_output=True)
   if r.returncode==0 and hashlib.sha256(r.stdout).hexdigest()==v['sha256']:matches.append(f)
 rows.append(dict(module=m,source_sha256=v['sha256'],revision=rev,git_matches=matches,basis='matching committed source' if matches else 'pinned external package source' if not re.fullmatch('[0-9a-f]{40}',rev) else 'REVIEW'))
(E/'SOURCE-GIT-AUDIT.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Sources:',len(rows),'git matches:',sum(bool(r['git_matches']) for r in rows),'review:',[r['module'] for r in rows if r['basis']=='REVIEW'])
