from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NEE_validate as v
base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');packet=v.read(E/'NEE_LEDGER_DELTA.json');review=v.read(E/'NEE_REVIEWED_CERTIFICATES.json')
spec=v.read(v.R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']
out=v.compose(base,packet,review);closed=[r['row'] for r in out['rows'] if r['function'] in spec['functions'] and r['composed_status']=='CLOSED']
packet['composed_rows_closed']=closed;packet['status']='Rule16: 6/97 composed rows CLOSED, 0/7 roots; suspended certificates retained for audit and rejected by validator'
(E/'NEE_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n')
p=v.read(E/'NEE_EDGES.json');p['composed_rows_closed']=closed
first=next(f for f in spec['roots'] if f.endswith('::validate_pool_v1_pair_forest_terminal_statement_v1'))
for edge in p['edges']:
 c=packet['edges'].get(edge['edge']);accepted=v.certificate(c,edge['edge'],base,review)
 edge['NEE_status']='CLOSED' if accepted else 'OPEN';edge['NEE_certificate']=c['id'] if accepted else None
 if not accepted:
  edge['NEE_obstacle']='Exact native child frame/domain/physical certificate is not accepted. Model transport is separate. '+('Historical certificate references a rule16-suspended receipt.' if v.suspended_reference(c) else edge.get('NEE_obstacle',edge['obstacle']))
 if edge['caller']==first:
  edge['NEE_native_caller_support']=['NEE_K052','NEE_K053']
  edge['NEE_model_support']=['NEE_OracleCallDomains.payment_same','NEE_OracleCallDomains.lane_same','NEE_OracleCallDomains.late_domain','NEE_ReachedRootModel.result_and_effects']
  edge['NEE_obstacle']='Ruling-(y) caller control has local-record support K052/K053; model same-argument facts and reached-only substitution are proved. Part (2) still needs the selected child physical instance and exact native frame; common/parts direct harness modules are suspended, borrowed admission is OPEN, payment encode_common frame timed out K054/K055, and remaining lane/late frames are not certified.'
for edge in p.get('supplemental_inventory_edges',[]):
 if isinstance(edge,dict):
  key=edge.get('edge',edge.get('subject',''));c=packet.get('inventory_edges',{}).get(key)
  edge['NEE_status']='CLOSED' if v.certificate(c,key,base,review) else 'OPEN'
  if edge['NEE_status']=='OPEN':edge['NEE_certificate']=None
(E/'NEE_EDGES.json').write_text(json.dumps(p,indent=1)+'\n')
old=v.read(v.R/'evidence/slice-s-compose-20261029/NED_REMAINING.json')
active=v.read(v.R/'evidence/slice-s-compose-20261029/NED_ACTIVE_PROOFS.json')['active']
texts={x['module']:(v.R/'evidence/slice-s-compose-20261029'/x['source']).read_text() for x in active}
deps={f:set() for f in spec['functions']}
for e in spec['internal_edges']:
 a,b=e.split(' -> ');deps[a].add(b)
reachable=set();todo=[first]
while todo:
 f=todo.pop()
 if f in reachable:continue
 reachable.add(f);todo.extend(deps.get(f,set()))
rows={f:[r for r in out['rows'] if r['function']==f] for f in spec['functions']}
stop=[]
for m in old['members']:
 f=m['function'];rs=rows[f];current=all(r['composed_status']=='CLOSED' for r in rs)
 matching=[dict(module=x['module'],source='evidence/slice-s-compose-20261029/'+x['source'],theorems=x['theorems'],receipt=x['receipt']) for x in active if f.split('::')[-1] in texts[x['module']]]
 stop.append(dict(function=f,composed_status='CLOSED' if current else 'OPEN',first_root_conservative_dependency=f in reachable,
  why_no_further_attempt=('Already CLOSED with accepted static-free native, model and frame certificates.' if current else ('First-root work: native frame/physical/domain instance is unproved or rule16-suspended; 55/55 Kani exhausted. Additional pure model equality cannot establish that native instance. Specific retained obligations follow.' if f in reachable else 'Binding first-root order: cannot start another root while validator is OPEN. Once allowed, its retained native/domain obligations below remain; no closure is inferred.')),
  retained_inner_hypotheses=m['inner_names_retained'],retained_internal_edges=m['internal_edges'],retained_selected_claims=m['exact_selected_claims'],native_obligation=m['further_native_work'],lean_obligation=m['further_lean_work'],reused_model_source_matches=matching,
  no_claim_that_lean_budget_exhaustion_closed_a_gap=True))
stopdoc=dict(slice='S',kani_used=55,kani_authorized=55,lean_used=30,lean_authorized=150,first_root=first,composed_rows_closed=closed,
 reason_for_under80percent_lean_stop='Kani exhaustion alone was not a stop: continued with arbitrary-reply call domains and reached-only substitution, compiled and audited them. The remaining first-root deficits require native framed child instances; neither a pure model equality nor an additional assumption is a valid replacement. Other roots are barred by the binding finish-one-root order. Every member retains its exact named and edge obligations below; no assertion that all Lean obligations are discharged is made.',members=stop)
(E/'NEE_STOP_AUDIT.json').write_text(json.dumps(stopdoc,indent=1)+'\n')
roots={f:[r['composed_status'] for r in rows[f]] for f in spec['roots']}
(E/'NEE_VALIDATION_SUMMARY.json').write_text(json.dumps(dict(slice_closed=closed,roots=roots,inherited_checks_preserved=True),indent=1)+'\n')
(E/'NEE_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n')
statement=(E/'NEE_ReachedRootModel.lean').read_text().split('theorem result_and_effects',1)[1].split(' := by',1)[0]
rootrows='\n'.join('| '+f.split('::')[-1]+' | 0 | OPEN |' for f in spec['roots'])
(E/'NEE_COMPOSED.md').write_text('''# Slice S composition after rule 16

**6/97 composed rows CLOSED; 0/7 roots CLOSED. Target not yet established.**
This supersedes the 12/97 stage-3 claim and intermediate 10/97 figure.
Frozen source: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline
AspisR1.RPx_Deployed.deployed on the coherent SInt2 owners. The six accepted
rows are transfer_common, withdrawal_common and payment digest_is_canonical
in TX1/TX2. See NEE_VALIDATION_SUMMARY.json and NEE_RULE16_AUDIT.md.

NativeContractSemanticTransport is P6/D188 option A RECLASSIFICATION, not trust
removal. RuntimePersistence, the approved trust rows, L154, privacy, 100-bit
per-attempt soundness and the two-transaction design are unchanged.

| Slice root | Composed rows CLOSED | Status |
|---|---:|---|
'''+rootrows+'''

No native-root theorem with the authorized hypothesis list has been proved.
No model function is relabelled as frozen native code. The other six roots
were not started, following the binding first-root order.

## First root: caller support and exact model theorem

K052/K053 pass/fail the original oracle_domain_positive/negative properties
with harness-local records, arbitrary full child Results, exact argument
checks, full 1520-byte mutable reply havoc and ordered call logging. Both
positive branch covers are reached. The exact source projection is recorded
in NEE_LOCAL_VALIDATOR_PROJECTION.json; per-attempt patches are authoritative.
This is ruling-(y) caller support, not part-(2) child-frame discharge.
K054 and its smaller prefix split K055 timed out; neither earns credit.

The complete new MODEL statement is NEE_ReachedRootModel.result_and_effects:

```lean
theorem result_and_effects'''+statement+'''
```

The explicit remaining inner laws are payment_bridge, output_lane_bridge and
late_bridge on reached calls only. The final law compares the caller-observed
late status; NEE_ValidatorMutation proves arbitrary temporary-output mutation
is discarded. No root output equality is hidden inside PhysicalInterpretation.
This model theorem alone supplies NO native child instance or frame.

NEE_L029 checks this statement; NEE_L024 checks six arbitrary-reply domain/
ordered-prefix facts, including exact same nullifier and 1520-byte late prestate.
NEE_L028 checks reached-only substitution through rejection, child errors and
divergence. NEE_L025..027 failed elaboration drafts are retained and excluded.
Accepted new theorems use only [propext, Classical.choice, Quot.sound].
NEE_L030 is the one final focused axioms audit, not a full frozen replay.

The reused complete raw validator cohort equality remains
NEE_RawValidatorCohort.result (L017): for every typed model statement s,
rawValidator (NED_ReconstructCarriers.toRaw s) equals ok of the mapped complete
NED_ValidatorStatus.status s. Its only input is typed s; its printed axioms
are the standard three. This is an emitted/model equality, not native credit.

## Remaining native obligations

Common getter and tuple projection: historical direct oracle MODULES contain
written statics and are conservatively suspended; borrowed stub_verified
admission also lacks a semantic unimplied control (K039 is codegen failure).
Payment encoders: exact encode_common indexed native frame remains OPEN after
K054/K055; full callers' own frames/Results remain to be composed. Output-lane
and late encoders: local-record one-step checks and model inductions do not
supply their remaining selected native child frames/physical instances.
NEE_EDGES.json retains all 129 internal edges with certificates or obstacles;
NEE_STOP_AUDIT.json lists every one of the 61 members, retained inner names,
model source matches and exact native/Lean continuation obligations.

Budgets: 55/55 Kani, 30/150 Lean. Kani exhaustion was followed by Lean-only
work. No further pure model statement can substitute for an unproved native
frame; the member-by-member stop audit explains the under-80% Lean stop.
''')
print('rows',closed,'members',len(stop),'first-root conservative members',len(reachable))
