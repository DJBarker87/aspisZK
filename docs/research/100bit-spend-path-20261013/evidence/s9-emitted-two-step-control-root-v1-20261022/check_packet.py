from pathlib import Path
import json,hashlib,re
p=Path(__file__).resolve().parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();m=json.loads((p/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
for row in m['modules']:
 r=json.loads((p/row['receipt']).read_text());pre=json.loads((p/row['preflight']).read_text());cmd=json.loads((p/row['command']).read_text());log=(p/row['raw_log']).read_text()
 assert r==row['metrics'] and r['exit_status']==0 and r['watchdog_abort'] is None and r['foreign_lean_samples']==[] and r['process_swaps']==0
 assert sha(p/row['source'])==row['source_sha256']==r['source_sha256']==pre['source_sha256']
 assert r['object_sha256']==row['external_object_sha256']
 assert r['source_revision_at_launch']==pre['source_revision']
 assert r['controller_sha256']==sha(p/'run_focused.py')
 assert 'LEAN_PATH='+(p/row['profile']).read_text().strip() in cmd['argv']
 assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
 assert 'sorryAx' not in log and not re.search(r': error(?:\(|:)',log)
 if row['tag']=='consumer':
  for theorem in m['audited_in_consumer']:
   found=re.findall("'"+re.escape(theorem)+r"' depends on axioms:\s*\[(.*?)\]",log,re.S)
   assert len(found)==1,theorem
   assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',found[0]))==set(m['axioms'])
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/\-.*?\-/', '',(p/row['source']).read_text(),flags=re.S))
 assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)',(p/row['source']).read_text())
assert sha(p/m['dependency_source']['path'])==m['dependency_source']['sha256']
for suffix in ['*.olean','*.elf','*.so','*.pyc']:assert not list(p.rglob(suffix))
for line in (p/'SHA256SUMS').read_text().splitlines():
 digest,rel=line.split('  ',1);assert sha(p/rel)==digest,rel
print('PASS: emitted S9 two-step control; successful-helper/arithmetic and Rust library closure remain OPEN')
