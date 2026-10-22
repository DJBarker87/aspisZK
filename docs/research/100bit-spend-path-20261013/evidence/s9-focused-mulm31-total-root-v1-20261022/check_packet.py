#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,re
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text());r=json.loads((p/m['launch_receipt']).read_text());pre=json.loads((p/m['preflight']).read_text());cmd=json.loads((p/m['launch_command']).read_text());log=(p/m['lean_raw_log']).read_text()
assert m['schema']=='focused-extractor-proof-packet-v1'
assert r==m['launch_metrics'] and r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None
assert r['source_sha256']==pre['source_sha256']==m['source_sha256']==sha(p/m['source'])
assert r['object_sha256']==m['external_object_sha256']
assert r['source_revision_at_launch']==pre['source_revision']==m['source_revision_at_launch']
assert 'LEAN_PATH='+(p/m['profile']).read_text().strip() in cmd['argv']
assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
for d in m['dependencies']:
 assert sha(p/d['source'])==d['source_sha256']
 if d['object_pin'] is not None:assert pre['direct_imports'][d['module']]==d['object_pin']
for name, axioms in m['theorems'].items():
 reports=re.findall("'"+re.escape(name)+r"' depends on axioms:\s*\[(.*?)\]",log,re.S)
 assert len(reports)==1,name
 assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',reports[0]))==set(axioms)=={'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log and not re.search(r': error(?:\(|:)',log)
s=(p/m['source']).read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/\-.*?\-/', '',s,flags=re.S))
assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)',s)
assert m['compiled_objects_included'] is False
for suffix in ['*.olean','*.elf','*.so','*.pyc']:assert not list(p.rglob(suffix)),suffix
for line in (p/'SHA256SUMS').read_text().splitlines():
 digest,rel=line.split('  ',1);assert sha(p/rel)==digest,rel
print('PASS: actual S9 scalar multiplication totality and exactness, standard axioms, source/receipt pins')
