from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
out=[]
for a,count,expected in [('NIZ_K005',17,'(reply == 0) != (a == b)'),('NIZ_K007',28,'(reply == 0) != (a == b)'),('NIZ_K008',32,'bytes[observer] == frame')]:
 p=E/a/'receipt.json';d=json.loads(p.read_text());s=(E/a/'stdout.log').read_text()
 assert d['exit_status']==1 and f'1 of {count} failed' in s and 'Failed Checks: assertion failed: '+expected in s and 'timed out' not in s,a
 out.append(dict(attempt=a,receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),semantic_control=True,intended_check=expected,failed_checks=1,total_checks=count))
(E/'NIZ_CONTROLS.json').write_text(json.dumps(out,indent=2))
print('Three exact semantic controls validated read-only; no solver rerun.')
