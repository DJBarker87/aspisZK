#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent; sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text()); assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for e in m['entries']:
 r=json.loads((p/e['receipt']).read_text()); pre=json.loads((p/e['preflight']).read_text()); cmd=json.loads((p/e['command']).read_text()); log=(p/e['log']).read_text(); s=(p/e['source']).read_text()
 assert r==e['launch_metrics'] and r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None and r['foreign_lean_samples']==[]
 assert sha(p/e['source'])==e['source_sha256']==r['source_sha256']==pre['source_sha256'] and r['source_revision_at_launch']==pre['source_revision']
 assert r['controller_sha256']==pre['controller_sha256']==sha(p/'run_focused.py') and 'LEAN_PATH='+(p/e['profile']).read_text().strip() in cmd['argv']
 assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400' and r['object_sha256'] and pre['direct_imports']
 found={n:re.findall(r'[A-Za-z][A-Za-z0-9_.]*',a) for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",log,re.S)}; assert found==e['theorems']
 assert set(found)=={'AspisR1S9BodyPrefixPolynomialSumsV1.body_prefix_sums_match_source_polynomials'}
 for ax in found.values(): assert set(ax)<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in log and not re.search(r': error(?:\(|:)',log)
 u=re.sub(r'/\-.*?\-/', '',s,flags=re.S);u=re.sub(r'--[^\n]*','',u);assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',u)
 assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)',u)
for ext in ['*.olean','*.elf','*.so','*.pyc']:assert not list(p.rglob(ext))
for line in (p/'SHA256SUMS').read_text().splitlines(): d,rel=line.split('  ',1);assert sha(p/rel)==d,rel
print('PASS: source polynomial sum theorem, exact focused receipt, import pins and standard axioms verified; no object included')
