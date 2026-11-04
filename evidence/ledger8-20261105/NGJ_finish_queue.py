from pathlib import Path
import subprocess,json,re
E=Path(__file__).resolve().parent
assert (E/'NGJ_L025/receipt.json').exists(),'First queue still running'
jobs=[(31,'lean','NGJ_PoolProofDriver'),(32,'link','NGJ_PoolProofDriver'),(33,'audit','poolfixtures'),(34,'audit','poolroots'),(35,'lean','NGJ_PoolDriver'),(36,'link','NGJ_PoolDriver'),(37,'audit','poolscan'),(38,'lean','NGJ_ROOT_S'),(39,'lean','NGJ_ROOT_Q'),(40,'lean','NGJ_ROOT_HEADLINE')]
for i,k,t in jobs:
 a=f'NGJ_L{i:03}'
 if (E/a/'receipt.json').exists():continue
 # Every authored module is represented by a source-derived import baseline.
 p=E/'NGJ_EXPECTED_IMPORTS.jsonl';table={r['module']:r['imports'] for r in map(json.loads,p.read_text().splitlines())}
 for f in E.glob('NGJ_*.lean'):table[f.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',f.read_text(),re.M)))
 if t=='poolscan':
  for f in Path('evidence').glob('pool-retdata*-20261104/**/*.lean'):
   if '/sources/' in str(f) or f.stem.startswith(('NFV_','NFR_','NFO_')):
    m=f.stem
    if m not in table:table[m]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',f.read_text(),re.M)))
 p.write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(table.items())))
 with (E/(a+'.client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGJ_run.py'),a,k,t],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode and i not in [27,28,37]:break
