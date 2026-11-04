#!/usr/bin/env python3
"""Receipt-only mapping; exact semantic anchors plus ledger canonical edges."""
import collections, hashlib, json, lzma, pathlib, subprocess
D=pathlib.Path(__file__).resolve().parent
ROOT=D.parent.parent
LP='evidence/ledger6-20261104/NFK_LEDGER.json.xz'
ledger=json.loads(lzma.open(ROOT/LP).read())
slices=json.loads((ROOT/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text())['slices']
rows=ledger['rows']
# Exact, reviewed subject cuts. No fuzzy matching, substring inference, or traversal
# of discovery_mentions: those are search hints, not frozen call-graph evidence.
C='crates/aspis-r1-cost-probe/src/'
P='programs/r1-cost-probe/src/'
def ids(file,*names): return [file+'::'+n for n in names]
anchors={
'S1': ids(C+'candidate.rs','prepare')+ids(C+'verifier.rs','Prepared::new','prepared_claim'),
'S2': ids(P+'lib.rs','process_r1_cost_probe_instruction')+ids(P+'pool_route.rs','admitted')+ids(P+'r1_pool_adapter.rs','process')+ids(P+'r1_pool_adapter_owned.rs','stage1','stage2','stage1_owned','stage2_owned')+ids(C+'candidate.rs','parse_shape','tx1','tx2_authenticated','tx2_common'),
'S3': ids(C+'weights.rs','Weights::pair')+ids(C+'r1_semantic.rs','semantic_boundary','semantic_rounds','verify_finish'),
'S4': ids(C+'fast_dots.rs','four_dots'),
'S5': ids(C+'fast_pairing.rs','EbyKDot::new','EbyKDot::push','EbyKDot::finish','canonical::Dot::new','canonical::Dot::push','canonical::Dot::finish','checked_q')+ids(C+'verifier.rs','finish_relation','finish_relation_round')+ids('crates/aspis-core/src/field.rs','M31::from_le_bytes','CM31::from_le_bytes','QM31::from_le_bytes'),
'S6': slices['S']['roots']+ids(C+'verifier.rs','checkpoint','resume')+ids(C+'candidate.rs','tx1'),
'S7': slices['Q']['roots']+ids(C+'verifier.rs','BatchedWeights::new','BatchedWeights::finish','BatchedWeights::value'),
'S8': ids(C+'verifier.rs','Accumulator::new','update_residue_row','finish_query_dot')+ids(C+'compact.rs','check_values','compact_row','expand_semantic','expand_values'),
'S9': ids(C+'weights.rs','factored_s2_libra_weights'),
'S10': []}
reasons={
'S1':'Preparation owner and same Prepared/claim/scratch inputs; candidate prepare calls Prepared::new and prepared_claim through recorded edges.',
'S2':'Native entry, route/header admission and adapter/TX dispatch; descendants are caller prerequisites, not a proof of runtime history association.',
'S3':'Complete pair and semantic boundary/round/terminal consumers, carrying SAME final values and EquationEndpoint interpretation.',
'S4':'Four width-29 opening dots at the SAME query opening; U07/dots domains retain gamma, canonical fields and term bounds.',
'S5':'Strict field decode, tower/pair/dot and finish-round kernels; reached operand/Result semantics remain part of the caller domain.',
'S6':'Public/statement/Claims decoder and TX1/checkpoint writer/resumer; S roots include statement reconstruction, proof scan and emitted result bytes.',
'S7':'Query-loop and geometry roots plus batched accumulation state; SAME phase, query, inverses, powers and 64-row updates.',
'S8':'Accumulator initialization, residue traversal, compact expansion/check and final accumulated query dot; not a parser/multiproof renaming.',
'S9':'Factored Libra coefficient construction; low/high/grouped helpers are assigned only when reached by the frozen factored root.',
'S10':'All frozen source sites/continuations, including errors. A function occurrence is a coverage site, not an artifact/replay certificate.'}
bytx={t:{r['function']:r for r in rows if r['transaction']==t} for t in ['TX1','TX2']}
paths={}
for cone, seeds in anchors.items():
 for tx, index in bytx.items():
  found={f:[f] for f in seeds if f in index}; q=collections.deque(found)
  while q:
   f=q.popleft()
   for g in index[f]['canonical_callees']:
    if g in index and g not in found:
     found[g]=found[f]+[g];q.append(g)
  paths[cone,tx]=found
result=[]
for r in rows:
 assignments=[]
 for cone in anchors:
  path=paths[cone,r['transaction']].get(r['function'])
  if cone=='S10':path=[r['function']]
  if path:
   assignments.append({'cone':cone,'role':'all-site inventory' if cone=='S10' else ('subject anchor' if len(path)==1 else 'transitive prerequisite'), 'reason':reasons[cone], 'frozen_call_path':path})
 result.append({'row':r['row'],'transaction':r['transaction'],'function':r['function'],'source_line':r['source_line'],'frozen_body_sha256':r['frozen_body_sha256'],'composed_status':r['composed_status'],'slices':[s for s in slices if r['function'] in slices[s]['functions']], 'assignments':assignments,'no_cone_reason':None if assignments else 'No subject anchor or recorded canonical call path.', 'trust_rows':{k:r.get(k,[]) for k in ['trust_rows','NEZ_trust_rows','NFK_trust_rows']}, 'support_receipts':r['active_support_receipts'],'premise_discharge':'NONE newly established: occurrence status is not an Rc7 premise-domain retirement.'})
summary={}
for cone in anchors:
 rr=[r for r in result if any(a['cone']==cone for a in r['assignments'])]
 subject=[r for r in rr if r['function'] in anchors[cone]]
 summary[cone]={'total':len(rr),**{s:sum(r['composed_status']==s for r in rr) for s in ['CLOSED','QUALIFIED','OPEN']}, 'slice_occurrences':sum(bool(r['slices']) for r in rr), 'subject_rows':[r['row'] for r in subject], 'subject_in_slices':[r['row'] for r in subject if r['slices']], 'subject_counts':dict(collections.Counter(r['composed_status'] for r in subject))}
inputs=[LP,'evidence/ledger6-20261104/NFK_LEDGER.json.sha256','evidence/ledger6-20261104/NFK_LEDGER.md','design/S1-S10-CLOSURE-MAP-20261026.md','evidence/recount7-20261026/Rc7_premises.json','docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.md','docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json']
out={'schema_version':1,'headline':'Numbers are status, not new credit. Target not yet established.','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'frozen_rust_revision':ledger['frozen_revision'],'ledger_source_revision':ledger['NFK_source_revision'],'input_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in inputs},'uncompressed_ledger_sha256':hashlib.sha256(lzma.open(ROOT/LP).read()).hexdigest(),'method':'Exact subject anchors reviewed against canonical obligations and inventory domains; shortest directed canonical_callees path within each transaction. Conservative alternatives and recursion retained. Paths establish dependency coverage only; no source-model or historical-statement identity inferred. S10 covers all sites by definition.','anchors':{k:{'functions':v,'reason':reasons[k]} for k,v in anchors.items()},'global_counts':dict(collections.Counter(r['composed_status'] for r in result)),'cone_counts':summary,'no_cone_rows':[r['row'] for r in result if not r['assignments']],'only_S10_rows':[r['row'] for r in result if [a['cone'] for a in r['assignments']]==['S10']],'rows':result}
(D/'NFL_ROW_TO_CONE.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(summary,indent=2));print('only S10',len(out['only_S10_rows']))
