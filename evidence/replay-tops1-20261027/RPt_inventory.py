"""Static source/evidence pins and progress; no proof execution."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;R=E.parents[1]
p=json.loads((E/'RPt_plan.json').read_text()); checks=[]
for r in p['rows']:
 old=(R/r['original_source']).read_text();new=(R/r['source']).read_text()
 canon=lambda s:re.sub(r'^import .*\n','',s,flags=re.M)
 assert canon(old)==canon(new),r['original']
 checks.append({'original':r['original'],'original_sha256':hashlib.sha256(old.encode()).hexdigest(),'snapshot_sha256':hashlib.sha256(new.encode()).hexdigest(),'only_imports_changed':True})
(E/'RPt_source-check.json').write_text(json.dumps(checks,indent=2)+'\n')
for n,job in [('FJp','finish-match4'),('FJu','finish-chain1')]:
 path=R/f'evidence/{job}-20261027/{n}_statement-check.json'
 (E/f'RPt_{n}-statement-evidence-pin.json').write_text(json.dumps({'path':str(path.relative_to(R)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'bytes':path.stat().st_size,'fresh_kernel_comparison':'pending, root closure exceeds run budget'},indent=2)+'\n')
for root in p['roots']:
 text=(R/'lean'/(root+'.lean')).read_text();statement=text[text.index('theorem deployed'):text.index(' := by')]
 (E/f'RPt_{root}.source-statement.txt').write_text(statement+'\n')
print('Verified import-only snapshots:',len(checks))
