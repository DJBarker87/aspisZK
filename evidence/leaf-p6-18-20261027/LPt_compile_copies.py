from pathlib import Path
import json,subprocess,sys,hashlib,re
E=Path(__file__).resolve().parent
rows=json.loads((E/'LPt_COPY_PLAN.json').read_text())['modules']
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('LPt_L*/receipt.json'))]
latest={r['module']:r for r in receipts if r['exit_status']==0};changed=set()
n=max([int(r['attempt'].split('L')[-1]) for r in receipts]+[0])
for row in rows:
 m=row['module'];p=Path('lean')/(m+'.lean');r=latest.get(m)
 deps=re.findall(r'^import (\S+)',p.read_text(),re.M)
 if r and row['sha256'] in r['source_hashes'].values() and not changed.intersection(deps):continue
 n+=1;a=f'LPt_L{n:03d}'
 result=subprocess.run([sys.executable,str(E/'LPt_build.py'),a,str(p),m])
 if result.returncode or json.loads((E/a/'receipt.json').read_text())['exit_status']:
  raise SystemExit('STOP '+a)
 changed.add(m)
 if m=='LPt_LPl_Kit_FunsExternal':
  n+=1;a=f'LPt_L{n:03d}'
  result=subprocess.run([sys.executable,str(E/'LPt_build.py'),a,'lean/LPt_Coimport.lean','LPt_Coimport'])
  if result.returncode or json.loads((E/a/'receipt.json').read_text())['exit_status']:raise SystemExit('STOP '+a)
