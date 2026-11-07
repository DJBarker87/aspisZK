"""Prepare only current own revision2 roots; preserve historical audit inputs."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
seen=set();order=[]
def visit(n):
 if n in seen:return
 seen.add(n);p=E/(n+'.lean')
 if not p.exists():return
 for d in re.findall(r'^import (\w+)',p.read_text(),re.M):visit(d)
 order.append(n)
visit('NMS_R2_COMBINED_IMPORT')
rows=[json.loads(l) for l in (E/'NMS_ATTEMPTS.jsonl').read_text().splitlines()]
roots=[];inputs=[]
for module in order:
 if not module.startswith('NMS_R2') or module in ['NMS_R2_COMBINED_IMPORT','NMS_R2Driver']:continue
 p=E/(module+'.lean');h=hashlib.sha256(p.read_bytes()).hexdigest()
 matches=[r for r in rows if r.get('module')==module and r.get('exit_status')==0 and h in r.get('source_hashes',{}).values()]
 assert matches,'Unaccepted current module '+module
 r=matches[-1]
 for line in r['print_axioms']:
  m=re.match(r"'([^']+)' (depends on axioms|does not depend on any axioms)",line)
  if m and m[1].startswith('NMS_R2') and m[1] not in roots:roots.append(m[1])
 inputs.append(dict(module=module,source_sha256=h,attempt=r['attempt'],receipt=r['full_receipt']))
manifest=dict(scope='Only current own revision2 theorem roots in focused import; no basis/ledger root audit',groups=[roots[i:i+7] for i in range(0,len(roots),7)],source_acceptance=inputs)
(E/'NMS_R2_AUDIT_ROOTS.json').write_text(json.dumps(manifest,indent=1)+'\n')
expected={}
for line in (E/'NMS_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
 row=json.loads(line);expected[row['module']]=row
for n in order:
 if n.startswith('NMS_R2'):
  deps=['Init']+re.findall(r'^import (\w+)',(E/(n+'.lean')).read_text(),re.M)
  expected[n]=dict(module=n,imports=list(dict.fromkeys(deps)))
(E/'NMS_R2_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[k])+'\n' for k in sorted(expected)))
print(json.dumps(dict(roots=len(roots),groups=len(manifest['groups']),modules=len(inputs))))
