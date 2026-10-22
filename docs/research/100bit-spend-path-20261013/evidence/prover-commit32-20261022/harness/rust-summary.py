#!/usr/bin/env python3
"""Join each raw receipt to its immutable source/input pin reference."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent.parent
rows=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 name=p.parent.name;rec=json.loads(p.read_text());pin=E/'pins'/(name+'-inputs.json')
 row=dict(name=name,receipt_path=str(p.relative_to(E)),**rec)
 if pin.exists():
  data=json.loads(pin.read_text())
  row.update(source_revision=data['source_revision'],inputs_path=str(pin.relative_to(E)),inputs_sha256=hashlib.sha256(pin.read_bytes()).hexdigest())
 elif name.startswith('build-'):
  pin=E/'pins/frozen-elf-final-check.json';data=json.loads(pin.read_text())
  row.update(source_revision=data['source_revision'],inputs_path=str(pin.relative_to(E)),inputs_sha256=hashlib.sha256(pin.read_bytes()).hexdigest())
 else:raise AssertionError(name)
 if rec['exit_status']==124:
  row['rss_caveat']='GNU time may report only the wrapper when timeout kills descendants; retain cgroup_memory_peak_bytes as the aggregate scope memory measurement, not as process RSS.'
 rows.append(row)
(E/'rust-receipts.jsonl').write_text(''.join(json.dumps(row,sort_keys=True)+'\n' for row in rows))
print('Joined',len(rows),'completed receipts; unfinished checks are omitted.')
