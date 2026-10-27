"""Verify archived code inputs against the applied git revision, read-only."""
from pathlib import Path
import hashlib,json,subprocess
D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';rev='5b92d4aa185486cc735c0a3eb75a3024171ca482'
script="""from pathlib import Path
import hashlib,json
R=Path('"""+D+"""/candidate/src')
rows=[]
for p in sorted(R.rglob('*')):
 if p.is_file():rows.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(rows))
"""
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True,capture_output=True,check=True);rows=json.loads(r.stdout);bad=[]
for row in rows:
 b=subprocess.check_output(['git','show',rev+':'+row['path']]);row['matches_revision']=hashlib.sha256(b).hexdigest()==row['sha256']
 if not row['matches_revision']:bad.append(row['path'])
E=Path('evidence/pv-batch2-20261027');(E/'SOURCE-IDENTITY.json').write_text(json.dumps(dict(revision=rev,files=rows,mismatches=bad,passed=not bad),indent=2)+'\n');assert not bad,bad
print('Verified',len(rows),'archived files at',rev)
