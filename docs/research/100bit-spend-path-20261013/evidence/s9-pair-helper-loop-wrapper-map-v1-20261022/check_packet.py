#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
P=Path(__file__).resolve().parent
m=json.loads((P/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
for label,e in m['entries'].items():
 rec=json.loads((P/e['receipt']).read_text()); src=P/e['source']
 assert hashlib.sha256(src.read_bytes()).hexdigest()==e['source_sha256']==rec['source_sha256'], label+' source hash'
 assert rec['object_sha256']==e['object_sha256'] and rec['exit_status']==0 and rec['process_swaps']==0, label+' receipt'
 assert rec['source_revision_at_launch']==e['source_revision_at_launch']
 assert sorted(e['axioms'])==sorted(['propext','Classical.choice','Quot.sound']), label+' axiom set'
 log=(P/e['log']).read_text(); assert all(a in log for a in e['axioms']), label+' axioms log'
 cmd=json.loads((P/e['command']).read_text()); argv=cmd['argv']; assert argv[-1].endswith(e['module']+'.lean'), label+' command source basename'
 pre=json.loads((P/e['preflight']).read_text()); assert pre['target']==e['module'] and pre['source_sha256']==e['source_sha256'], label+' preflight pin'
for f in P.rglob('*'):
 if f.is_file():
  assert not f.name.lower().endswith(('.olean','.ilean','.so','.dylib','.dll','.o','.a')), f'compiled artifact: {f}'
for line in (P/'SHA256SUMS').read_text().splitlines():
 h,rel=line.split('  ',1); assert hashlib.sha256((P/rel).read_bytes()).hexdigest()==h, rel+' checksum'
print('PASS: success-conditional helper and wrapper maps, source/receipt pins, standard axioms, and source-only checks')
