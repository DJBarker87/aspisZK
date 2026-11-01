"""Read-only recovery after stopping an own local dispatcher; never submit."""
from NEK_host import *
from NEK_verdict import verdict
import sys
for a in sys.argv[1:]:
 r=py(f'''from pathlib import Path
import json,base64,zlib
b=Path({B!r});p=b/{a!r};out={{n:(p/n).read_text() for n in ['receipt.json','stdout.log','time.log'] if (p/n).is_file()}}
out.update({{q.name:q.read_text() for q in b.glob({(a+'-*check.json')!r})}})
print(base64.b64encode(zlib.compress(json.dumps(out).encode())).decode())
''');assert r.returncode==0,r.stderr
 data=json.loads(zlib.decompress(base64.b64decode(r.stdout)));assert 'receipt.json' in data,a
 for n,t in data.items():
  p=E/a/n if n in ['receipt.json','stdout.log','time.log'] else E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
 rc=json.loads(data['receipt.json']);old=[json.loads(l)['attempt'] for l in (E/'NEK_ATTEMPTS.jsonl').read_text().splitlines()]
 if a not in old:
  with (E/'NEK_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
 plan=json.loads((E/'NEK_COMMON_BATCH_PLAN.json').read_text());item=next(i for i in plan if i['attempt']==a);v=verdict(data['stdout.log'])
 if not any(json.loads(l)['attempt']==a for l in (E/'NEK_RESULTS.jsonl').read_text().splitlines()):
  with (E/'NEK_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,original_receipt=item['original_receipt'],verdict=v,expected='FAIL' if item['negative'] else 'PASS',negative=item['negative'],method='read-only recovery of submitted immutable v1 cfg window',clause=item['clause']))+'\n')
 print(a,rc['exit_status'],rc['wall_seconds'],v,'solver_started', 'Checking harness' in data['stdout.log'])
