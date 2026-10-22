#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).parent
err=[]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for line in (root/'SHA256SUMS').read_text().splitlines():
 h,rel=line.split('  ',1); p=root/rel
 if not p.is_file() or sha(p)!=h: err.append('hash mismatch/missing '+rel)
for rel,needles in [
 ('sources/S4TailParserWitnessEmbeddingV1.lean',['theorem first_query_exact_embedding','theorem contribution_exact_embedding','#print axioms first_query_exact_embedding','#print axioms contribution_exact_embedding']),
 ('sources/S4TailRunTraceScalarEmbeddingV1.lean',['theorem run_trace_scalar_embeddings','#print axioms run_trace_scalar_embeddings','trace_member_input_witness','trace_member_term_lt_two','termFin.val = c.term.val']),
 ('sources/S4TailSlotByteProjectionsV1.lean',['theorem c1_tail_source_slice','theorem c2_lane_source_slice']),
 ('dependencies/S4TailParserFixedArrayEmbeddingV1.lean',['theorem parser_success_exact_embedding']),
 ('dependencies/S4TailTraceMemberWitnessV1.lean',['theorem trace_member_input_witness','theorem trace_member_term_lt_two'])]:
 t=(root/rel).read_text()
 for n in needles:
  if n not in t: err.append(f'{rel} missing {n}')
# Reject the exact module self-shadowing that made attempt12 unsafe to import.
for rel,mod in [
 ('sources/S4TailParserWitnessEmbeddingV1.lean','S4TailParserWitnessEmbeddingV1'),
 ('sources/S4TailRunTraceScalarEmbeddingV1.lean','S4TailRunTraceScalarEmbeddingV1'),
 ('sources/S4TailSlotEmbeddingV1.lean','S4TailSlotEmbeddingV1'),
 ('sources/S4TailSlotByteProjectionsV1.lean','S4TailSlotByteProjectionsV1')]:
 if f'import {mod}' in (root/rel).read_text(): err.append(f'{rel} imports its own output module {mod}')
# Apply the self-import guard to every accepted Lean source named by this packet's
# source list; failed/retained diagnostics are intentionally excluded.
accepted_sources = [
 'sources/S4TailParserWitnessEmbeddingV1.lean',
 'sources/S4TailRunTraceScalarEmbeddingV1.lean',
 'sources/S4TailSlotEmbeddingV1.lean',
 'sources/S4TailSlotByteProjectionsV1.lean',
 'dependencies/S4TailParserFixedArrayEmbeddingV1.lean',
 'dependencies/S4TailTraceMemberWitnessV1.lean',
]
for rel in accepted_sources:
 t=(root/rel).read_text()
 module=Path(rel).stem
 if any(line.strip()==f'import {module}' for line in t.splitlines()):
  err.append(f'{rel} imports its own output module {module}')
for rec,expected in [('receipts/attempt15/receipt.json',0),('receipts/attempt18/receipt.json',0)]:
 d=json.loads((root/rec).read_text())
 if d['exit_status']!=expected or d['source_sha256_before']!=d['source_sha256_after']: err.append(rec+' invalid status/source hashes')
for rec,names in [('receipts/attempt15/lean.log',['first_query_exact_embedding','contribution_exact_embedding']),('receipts/attempt18/lean.log',['run_trace_scalar_embeddings']),('receipts/byte-axiom-audit-v1/lean.log',['parser_success_exact_embedding','c1_tail_source_slice','c2_lane_source_slice','current_qm_embedding'])]:
 t=(root/rec).read_text()
 if 'Classical.choice' not in t or 'Quot.sound' not in t: err.append(rec+' lacks standard axiom report')
 for name in names:
  if name not in t: err.append(rec+' lacks named axiom report for '+name)
log=(root/'receipts/attempt18/lean.log').read_text()
if 'run_trace_scalar_embeddings' not in log or 'termFin.val = c.term.val' not in (root/'sources/S4TailRunTraceScalarEmbeddingV1.lean').read_text(): err.append('attempt18 lacks the accepted term-linked whole-trace theorem')
# The renamed owner must directly import only the old fixed-array predecessor; no extension object is included.
pins=json.loads((root/'dependencies/attempt15-direct-import-pins.json').read_text())
old=next((x for x in pins['imports'] if x['module']=='S4TailParserEmbeddingV1'),None)
if not old or old.get('olean_sha256')!='9e90bbbccf021f4aada960d8facab6b90c61a0f15aa8014a78cd04dd696b6941': err.append('fixed-array predecessor pin mismatch')
# The rejected same-name extension is never promoted.
if not any('attempt12' in str(p.relative_to(root)) for p in (root/'diagnostics').rglob('*') if p.is_file()): err.append('attempt12 diagnostic missing')
if any(p.suffix in {'.olean','.ilean','.o','.dylib'} for p in root.rglob('*') if p.is_file()): err.append('binary artifact present')
if err: print('\n'.join(err)); sys.exit(1)
print('PASS: unique-module actual witness embeddings, run-trace consumer, exact axiom outputs, selected predecessor and diagnostic corrections verified; no binaries.')
