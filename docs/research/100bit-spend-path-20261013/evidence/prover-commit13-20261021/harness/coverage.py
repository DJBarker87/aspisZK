#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
x=json.loads((E.parent/'prover-commit12-20261021/callback-coverage.json').read_text())
x['source_revision']='9f6852af9'
x['kind']='All-family obligation ledger; not an execution or probability certificate'
x['all_family_coverage_closed']=False
for r in x['rows']:
 p=Path(r['source']);r['source_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 if r['family']=='mask stream':
  r['reference'] += ['state_only_hiding::scalar13::mask_scalar_partition','R1Z.ProverCommitScalarPartition.sixteen_partition']
  r['status']='actual complete scalar; outer material schedule open'
  r['remaining']='Actual material outer loop translation fails in Aeneas at lines 471-489. Collection-to-global-window composition and packing still require a concrete material reference instance.'
 if r['family']=='source/D stream':
  r['reference'] += [f'state_only_entropy::scalar13::source_word_{i}' for i in range(9)]
  r['status']='actual complete scalar over all nine word positions; D collection open'
  r['remaining']='All source scalar cases pass. Actual successful D collection and concrete global-window/material instance remain open.'
 if r['family'] in ['public digest','outer private-attempt binding']:
  r['reference']=['transcript::outer13::public_digest_and_binding_prefix']
  r['status']='literal secure prefix cut checked'
  r['remaining']='The concrete public serializer bound/image, nonce getter instance and following outer caller still need composition.'
 if r['family']=='intermediate source seed':
  r['reference']=['state_only_entropy::seeds13::source_inline_prefix','state_only_entropy::seeds13::source_seed_nonce_rejected','state_only_entropy::seeds13::source_seed_material_error']
  r['status']='literal frame and two actual rejection branches checked'
  r['remaining']='Actual successful source-seed wrapper and unconsumed returned-material disposal both reach their 600-second gates; excluded.'
 if r['family']=='D seed':
  r['reference']=['state_only_entropy::seeds13::d_seed_before_first_scalar']
  r['status']='actual method prefix to first scalar and propagated failure checked'
  r['remaining']='The successful 1024-element D collection, balancing, concrete caller arguments and global trace remain open.'
 if 'quer' in r['family'].lower():
  r['part13_caller_cut']='transcript::query13::result_and_retained_state'
  r['part13_scope']='All 17 callback frames, both buffers and complete caller result/state checked around an arbitrary sampler-result cut; sampler refinement and whole adaptive experiment not inferred.'
x['retained_obstructions']=[
 'The old local byte ROM has only four 514-byte points. Reused part-12 row-25 capacity certificate shows 3751 bytes for one semantic hash input.',
 'Per-stream nine-answer expander tables are restrictions of one global oracle only after the already-proved rebasing construction is concretely instantiated by the outer schedule.',
 'Callback observers prove framing for arbitrary traces, including consistent shared-oracle traces; they do not supply a joint adaptive execution coupling or a probability law.',
 'Actual outer material extraction v3 passes scalar/balancing opacity preflight, then fails at the Aeneas loop context join (471-489); no generated theorem is adopted.'
]
(E/'callback-coverage.json').write_text(json.dumps(x,indent=2)+'\n')
