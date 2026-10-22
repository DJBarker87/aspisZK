#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
for e in m['entries']:
 r=json.loads((p/e['receipt']).read_text()); pre=json.loads((p/e['preflight']).read_text()); cmd=json.loads((p/e['command']).read_text()); log=(p/e['log']).read_text(); s=(p/e['source']).read_text()
 assert r==e['launch_metrics'] and r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None and r['foreign_lean_samples']==[]
 assert sha(p/e['source'])==e['source_sha256']==r['source_sha256']==pre['source_sha256']
 assert r['source_revision_at_launch']==pre['source_revision']
 assert r['controller_sha256']==pre['controller_sha256']==sha(p/'run_focused.py')
 assert 'LEAN_PATH='+(p/e['profile']).read_text().strip() in cmd['argv']
 assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
 assert r['object_sha256'] and pre['direct_imports']
 assert not re.search(r': error(?:\(|:)',log) and 'sorryAx' not in log
 uncommented=re.sub(r'/\-.*?\-/', '',s,flags=re.S); uncommented=re.sub(r'--[^\n]*','',uncommented)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',uncommented)
 assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)',uncommented)
 a=e['axiom_audit']; ar=json.loads((p/a['receipt']).read_text()); ap=json.loads((p/a['preflight']).read_text()); ac=json.loads((p/a['command']).read_text()); alog=(p/a['log']).read_text(); asrc=(p/a['source']).read_text()
 assert ar==a['launch_metrics'] and ar['exit_status']==0 and ar['process_swaps']==0 and ar['watchdog_abort'] is None and ar['foreign_lean_samples']==[]
 assert sha(p/a['source'])==a['source_sha256']==ar['source_sha256']==ap['source_sha256']
 assert ar['source_revision_at_launch']==ap['source_revision'] and ar['controller_sha256']==ap['controller_sha256']==sha(p/'run_focused.py')
 assert 'LEAN_PATH='+(p/a['profile']).read_text().strip() in ac['argv']
 assert '-j1' in ac['argv'] and ac['argv'][ac['argv'].index('-M')+1]=='4400'
 found={n:re.findall(r'[A-Za-z][A-Za-z0-9_.]*',ax) for n,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",alog,re.S)}
 assert found==a['theorems'] and set(found)=={'AspisR1S9BodyOneRecordConsumerV1.side_one_source_tail_success','AspisR1S9BodyOneRecordConsumerV1.side_one_tail_math_witness_nonempty','AspisR1S9BodyOneRecordConsumerV1.side_one_prefix_tail_witness_nonempty','AspisR1S9BodyOneRecordConsumerV1.body_one_output_witness_nonempty','AspisR1S9BodyOneRecordConsumerV1.body_one_output_witness','AspisR1S9CandidateScalarFactorCallbackTransportV1.candidate_call_mut_maps'}
 for ax in found.values(): assert set(ax)<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r': error(?:\(|:)',alog) and 'sorryAx' not in alog
 au=re.sub(r'/\-.*?\-/', '',asrc,flags=re.S); au=re.sub(r'--[^\n]*','',au)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',au)
for ext in ['*.olean','*.elf','*.so','*.pyc']: assert not list(p.rglob(ext))
for line in (p/'SHA256SUMS').read_text().splitlines():
 digest,rel=line.split('  ',1); assert sha(p/rel)==digest,rel
print('PASS: BodyOne and callback sources, receipts, selected import pins and separate standard-axiom audit verified; compiled objects excluded')
