"""Name the remaining obligation per suspended original receipt."""
from NEH_scan import *
a=read_json(E/'NEH_APPLICABILITY.json');sources={r['receipt']:r for r in a['receipts']};d=read_json(E/'NEH_LEDGER_DELTA.json');out=[]
for r in d['receipts']:
 if r['outcome']!='OPEN':continue
 src=sources[r['receipt']];missing=src.get('missing_sources',[])
 if r.get('pair') and r['reason'].startswith('local native'):
  blocker='Direct selected value/frame and matched control checked; historical proof_for_contract composition not re-established with an explicit local-index context.'
  next_step='Check a local-context contract/native-step association in Kani, with interface-shape fidelity controls; reuse existing reference Lean facts. Do not relabel the direct observation as a function-contract certificate.'
 elif any(q['verdict']=='OPEN' for q in r['runs']):
  blocker='Incomplete solver run; inspect the exact failed target/timeout in retained stdout. No semantic counterexample and no credit.'
  next_step='Isolate the specific declaration or equality; change/split its proof shape and check both property and matched control. Never repeat a timeout or memory kill unchanged.'
 elif missing:
  blocker='Receipt-pinned source inputs remain unresolved.'
  next_step='Recover each missing exact hash, then preserve the original names/property in a static-free Kani replay plus matched failing control.'
 elif src.get('static_sites'):
  blocker='Static-bearing source closure has no completed same-property local-record replay and matched control.'
  next_step='Localize the exact reached state/log, preserve native-step association and caller domain, then check the same-name property and negative control with deployed features and frozen graph.'
 else:
  blocker='Macro/include or receipt input closure remains conservatively unresolved.'
  next_step='Resolve the pinned expansion/helper closure; replay unchanged native property and matched control in the verified KMX configuration if copies are reached.'
 name=Path(r['receipt']).parent.name
 if name in ['NDE_K050','NDE_K052','NDE_K071','NBG_K028','NBQ_K016']:
  blocker='Reached native-step/log association uses global capture; deleting the log or replacing it with an arbitrary successful stub changes the property.'
  next_step='Supply an explicit local-context native-step association and same-name Kani property/control. Multiplication logs additionally retain their named Lean arithmetic bridge; no multiplication proof in Kani.'
 if name in ['LPe_K001','LPe_K004','LPe_K005','LPe_K006','LPe_K007']:
  blocker='Historical grouped/buffer harness requires method review: multiplication and whole-buffer loops cannot be replayed wholesale under current rulings.'
  next_step='Split to a native single iteration/window on arbitrary pre-state, use existing KMX frame laws and Lean induction, and check native/model step association plus control; field multiplication remains Lean-discharged.'
 out.append(dict(receipt=r['receipt'],harness=r['harness'],dependent_rows=r['dependent_rows'],claims=r['claims'],blocker=blocker,next_step=next_step,missing_sources=missing,attempts=[v['attempt'] for v in r['runs']],requires_kani=True,lean_only_sufficient=False))
(E/'NEH_OPEN_OBLIGATIONS.json').write_text(json.dumps(dict(scope='Per-receipt K-3 suspension blockers, not a change to authoritative ledgers',members=out,lean_budget_note='No new Lean-only theorem can replace the missing native replay/control or certify unresolved compiler/source closure. Existing reference arithmetic and KMX value/frame laws are retained; new native-step shapes may create later Lean association work.'),indent=2)+'\n')
print(len(out),'OPEN receipt obligations recorded')
