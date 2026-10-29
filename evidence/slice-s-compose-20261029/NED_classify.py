"""Classify preserved conservative edges. No classification alone grants credit."""
import json,subprocess,hashlib
from pathlib import Path
E=Path(__file__).resolve().parent;d=json.loads((E/'NED_EDGES.json').read_text())
ledger=json.loads((E.parent.parent/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text())
for e in d['edges']:
 a,b=e['caller'],e['callee'];r=next(r for r in ledger['rows'] if r['function']==a)
 source=subprocess.check_output(['git','show',d['frozen_revision']+':'+r['source_file']]);span=r['frozen_body_byte_range']
 e['caller_source_pin']=dict(path=r['source_file'],revision=d['frozen_revision'],sha256=hashlib.sha256(source).hexdigest(),body_range=span,body_sha256=hashlib.sha256(source[span[0]:span[1]]).hexdigest())
 assert e['caller_source_pin']['body_sha256']==r['frozen_body_sha256']
 e['classification']='direct qualified call; typed domain and state/effect association required'
 if b.endswith('::to_le_bytes'):
  if a.endswith(('atomic_statement.rs::encode_digest_canonical','payment_relation.rs::encode_common')) and b.endswith('field.rs::M31::to_le_bytes'):
   e['classification']='genuine M31 serializer; all raw words, not a canonical-only field-product domain'
  elif 'WideExact::to_le_bytes' in a and b.endswith('field.rs::M31::to_le_bytes'):
   e['classification']='genuine M31 limb serializer selected by WideExact::to_limbs; prove eight limb/order associations'
  else:
   e['classification']='conservative alternative: primitive integer receiver or incompatible WideExact target; retain until typed source/extracted-body resolution certificate'
 if any('conservative' in str(x.get('resolution','')) or 'overapprox' in str(x.get('resolution','')) for x in e['sites']) and 'to_le_bytes' not in b:
  e['classification']='conservative method target; receiver owner needs explicit source/extracted carrier resolution'
 if not e['sites']:
  e['classification']='conservative union-only edge; no actual per-occurrence site in selected row, inspect other transaction and resolve before pruning'
 e['obstacle']='Per-edge native domain/physical/state/ordered-effect certificate not yet accepted. '+e['classification']
(E/'NED_EDGES.json').write_text(json.dumps(d,indent=1)+'\n')
from collections import Counter
print(json.dumps(Counter(e['classification'] for e in d['edges']),indent=1))
