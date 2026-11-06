from pathlib import Path
import json,hashlib
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((B/'NJG_EXPORT.json').read_text())
for r in x['files']:assert sha(Path(r['path']))==r['sha256'],r['path']
resolved=json.loads((B/'NJG_RESOLVED_OBJECTS.json').read_text())
for r in resolved:
 p=Path(r['path'])
 for suffix,size,h in r['parts']:
  q=p if suffix=='' else p.with_suffix('.ir') if suffix=='ir' else Path(str(p)+suffix)
  assert q.stat().st_size==size and sha(q)==h,str(q)
assert {'JFw_Validator','JFw_Record'} <= {r['module'] for r in x['files']}
assert any(r['module'].startswith('Aeneas') for r in resolved)
lock=B/'NJG_src/Cargo.lock';assert sha(lock)=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
pins=json.loads((B/'NJG_SOURCE_PINS.json').read_text());assert all(sha(B/'NJG_src'/n)==h for n,h in pins.items())
result=dict(status='PASS',retained_files=len(x['files']),resolved_modules=len(resolved),aeneas_modules=sum(r['module'].startswith('Aeneas') for r in resolved),frozen_lock_unchanged=True,scratch_source_pins_unchanged=True)
(B/'NJG_EXPORT_CHECK.json').write_text(json.dumps(result,indent=2));print(json.dumps(result))
