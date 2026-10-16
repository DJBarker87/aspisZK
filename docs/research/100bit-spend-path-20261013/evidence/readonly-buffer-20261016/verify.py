#!/usr/bin/env python3
"""Verify retained focused receipts, source pins and allowed axioms; no builds."""
from pathlib import Path
import hashlib,json,tarfile
p=Path(__file__).resolve().parent
pin=json.loads((p/'archive-pin.json').read_text());raw=(p/pin['path']).read_bytes()
assert len(raw)==pin['bytes'] and hashlib.sha256(raw).hexdigest()==pin['sha256']
with tarfile.open(p/pin['path']) as tf:
 def read(n):return tf.extractfile(n).read()
 summary=json.loads(read('check-summary.json'))
 assert summary==json.loads((p/'check-summary.json').read_text())
 assert len(summary['lean'])==4 and len(summary['native'])==2 and len(summary['extraction'])==2
 for kind in ['lean','native','extraction']:
  for r in summary[kind]:
   assert r['exit_status']==0,r
   assert r['limits']['memory.swap.max']=='0' and r['limits']['memory.max']=='8589934592'
   assert r.get('process_swaps',r.get('swaps'))==0
   if kind=='lean':
    for report in r['axioms_reports']:assert set(report['axioms'])<={'propext','Classical.choice','Quot.sound'}
 helper=next(r for r in summary['lean'] if r['target']=='ExtractedReadonlyMeta')
 assert len(helper['axioms_reports'])==8
 for r in helper['axioms_reports'][:3]:assert r['axioms']==['propext']
 audit=next(r for r in summary['lean'] if r['target']=='ReadonlyMetaGeneratedAudit')
 assert audit['axioms_reports'][-1]['declaration'].endswith('readonly_buffer_meta_ok')
 assert audit['axioms_reports'][-1]['axioms']==[]
 manifest=json.loads(read('inputs.json'))
 for name,digest in manifest['files'].items():assert hashlib.sha256(read(name)).hexdigest()==digest,name
 for attempt in ['helper-buffer-a','boundary-buffer-a','audit-buffer-a']:
  guard=json.loads(read(attempt+'-concurrency.json'));assert guard['initial_lean_processes']==[] and guard['external_events']==[]
 assert json.loads(read('concurrency-deviation.json'))['external_pid']==1613893
print('PASS:4 formal targets,2 native targets,2 extraction targets,519 source pins; runtime/SBF not run; concurrency deviation retained')
