#!/usr/bin/env python3
"""Slice definition: exact canonical-callee closure, same VERTICAL-SLICES schema.
No discovery-mention edges and no evidence/status promotion.
"""
import collections, hashlib, json, lzma, pathlib, subprocess
E=pathlib.Path(__file__).resolve().parent; R=E.parents[1]
LP='evidence/ledger6-20261104/NFK_LEDGER.json.xz'
SP='docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json'
raw=lzma.open(R/LP).read(); L=json.loads(raw); S=json.loads((R/SP).read_text())
rows=L['rows']; qs=set(S['slices']['Q']['functions'])|set(S['slices']['S']['functions'])
root='programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction'
paths={}; indexes={}
for tx in ['TX1','TX2']:
 ix={r['function']:r for r in rows if r['transaction']==tx};indexes[tx]=ix
 seen={root:[root]};queue=collections.deque([root])
 while queue:
  f=queue.popleft()
  for c in ix[f]['canonical_callees']:
   if c in ix and c not in seen:seen[c]=seen[f]+[c];queue.append(c)
 paths[tx]=seen
graph=collections.defaultdict(set)
for r in rows:graph[r['function']].update(r['canonical_callees'])
def closure(roots):
 seen={f:[f] for f in roots};queue=collections.deque(roots)
 while queue:
  f=queue.popleft()
  for c in sorted(graph[f]):
   if c in graph and c not in seen:seen[c]=seen[f]+[c];queue.append(c)
 return seen
global_paths=closure([root])
for name,spec in S['slices'].items():
 assert set(closure(spec['roots']))==set(spec['functions']),name
cone=set(global_paths); D=cone-qs
edges=sorted({f+ ' -> '+c for r in rows for f in [r['function']] if f in D for c in r['canonical_callees'] if c in D})
dr=[r for r in rows if r['function'] in D]
sl=dict(name='driver spine complement of Q and S (TX1+TX2)',roots=[root],functions=sorted(D),open_functions=sorted({r['function'] for r in dr if r['composed_status']!='CLOSED'}),internal_edges=edges,inventory_rows=[r['row'] for r in dr])
def put(n,o): (E/n).write_text(json.dumps(o,indent=2)+'\n')
put('NFQ_SLICE_D.json',dict(source=LP,frozen_revision=L['frozen_revision'],slices={'D':sl}))
coverage=[]
for r in rows:
 memberships=[s for s in ['Q','S'] if r['function'] in S['slices'][s]['functions']]+(['D'] if r['function'] in D else [])
 coverage.append(dict(row=r['row'],transaction=r['transaction'],function=r['function'],slices=memberships,status=r['composed_status'],frozen_call_path=paths[r['transaction']].get(r['function']),canonical_union_path=global_paths.get(r['function']),reason=None if memberships else ('Canonical graph omits map_err(error) callback edge. Frozen first_decoded calls map_err(error); callback is not a direct-call target in the inventory.' if r['function'].endswith('lib.rs::error') else 'No incoming path in the canonical union. Trait CodeField::from_m31 dispatch is not resolved to this inventory node; absence is a graph gap, not proof of non-reachability.')))
leaves=[('sampler.rs','low_base_p_digits','RESTORED'),('verifier.rs','echeck','INDEPENDENT'),('compact.rs','check_values','INDEPENDENT'),('r1_wire.rs','validate_record_fields','INDEPENDENT'),('verifier.rs','checkpoint','INDEPENDENT'),('compact.rs','expand_values','INDEPENDENT'),('r1_wire.rs',"ValidatedRecord<'a>::decode_k",'INDEPENDENT'),('r1_semantic.rs','claims','INDEPENDENT'),('fast_pairing.rs','canonical::Dot::push','INDEPENDENT'),('candidate.rs','wide_view','RESTORED'),('r1_semantic.rs','semantic_boundary','INDEPENDENT'),('sampler.rs','circle_sample','RESTORED'),('verifier.rs','prepared_claim','RESTORED')]
leafs=[]
for file,name,status in leaves:
 f='crates/aspis-r1-cost-probe/src/'+file+'::'+name
 assert f in cone,f
 rr=[r for r in rows if r['function']==f]
 leafs.append(dict(function=f,K2_status=status,in_D=f in D,rows=[r['row'] for r in rr],NFK_status={r['row']:r['composed_status'] for r in rr},packet='evidence/kani-k2leaf-20261028/KNF_FINDING.md',qualification='K-2 local-domain retention/restoration only; not automatic composed closure. Rule 16 and per-edge domains still required.'))
put('NFQ_LEAVES.json',leafs)
put('NFQ_COVERAGE.json',dict(frozen_revision=L['frozen_revision'],method='Canonical union of all transaction inventories, exactly reproducing Q=78 and S=61. D is the shared-entry closure minus Q/S. Per-transaction paths are diagnostics only; mixed-inventory union paths are conservative dependency witnesses, not same-run execution traces.',inputs={LP:hashlib.sha256((R/LP).read_bytes()).hexdigest(),SP:hashlib.sha256((R/SP).read_bytes()).hexdigest()},uncompressed_ledger_sha256=hashlib.sha256(raw).hexdigest(),counts=dict(total=len(rows),covered=sum(bool(r['slices']) for r in coverage),outside=sum(not r['slices'] for r in coverage),D_functions=len(D),D_edges=len(edges),D_rows=len(dr),D_status=dict(collections.Counter(r['composed_status'] for r in dr))),rows=coverage))
outside=[r for r in coverage if not r['slices']]
text=['# Slice D definition','', '**Definition and inherited status only. Target not yet established.**','',f'Frozen Rust `{L["frozen_revision"]}`. Baseline: NFK ledger (587 occurrences). D has **{len(D)} functions, {len(edges)} internal edges, {len(dr)} inventory rows**: '+str(dict(collections.Counter(r['composed_status'] for r in dr)))+'.', '', '## Exact deployed roots','',f'Both transaction roots are `{root}`. With deployed `pool-adapter`, TX1 instruction `[3,10]` or `[3,11]` dispatches through `pool_route::admitted`, `r1_pool_adapter::process`, `r1_pool_adapter_owned::stage1` / `stage1_owned`, and `lib.rs::first_decoded` to `candidate::tx1`. TX2 `ASQ8`-prefixed request data (not the disabled legacy `[4]` tag) dispatches through the same entry/adapter to `stage2` / `stage2_owned`, then `candidate::tx2_authenticated` / `tx2_common`. There is no separate deployed lib.rs second entry. `lib.rs::first` and direct `candidate::tx2` are in the disabled non-pool-adapter branch and absent from the frozen inventory.', '', 'The function set is the canonical UNION graph closure from the common deployed entry minus Q/S. This reproduces both original slices exactly (Q=78, S=61). The initial NFQ draft incorrectly used per-transaction closures, giving 291/441/339 and 581 covered rows; that draft is superseded. Q/S roots are opaque certification boundaries; their recorded descendants are used only to compute original inventory membership. No traversal through discovery mentions. Receiver-resolution overapproximations and recursive edges remain exactly as inventoried. Internal edges use the same sorted `caller -> callee` representation as VERTICAL-SLICES.', '', '## Inherited evidence is not new closure','', 'Twelve of the thirteen opaque leaf functions are in D (canonical::Dot::push is in Q). All 12 remain OPEN composed rows in NFK; local leaf restoration alone supplies no new CLOSED row. NFQ_LEAVES.json records every one of the 13 opaque packets and KNF K-2 status. KNF restores four affected local bridges; all 13 retain their local-domain credit. This does not establish every caller domain or repair writable-static support. The NFK composed statuses above remain authoritative. DrvI provides counterexamples to arbitrary-driver identity, not native closure; DrvC constructs the installed model and retires L160 only. Neither packet closes a new NDT occurrence here.', '', 'Later NFN removes the two geometry qualifications; NFM reports closed dots. Those functions belong to Q and remain separate from this D baseline. No duplicate row credit. RuntimeReturnData and RuntimeMemcmp are owner-accepted trust rows as of 2026-11-04; NFK historical pending wording is superseded, not discharged.', '', '## Slice boundary findings','', 'The Pool settlement consumer is not a node of the frozen 587-row verifier inventory. It cannot be silently added using this schema/tooling. Sibling NFO owns its native return-data packet. Pool-side settlement and same-instruction association remain explicit external boundaries.', '', 'The canonical graph omits the error callback edge (see NFQ_COVERAGE.md). No source/cfg(kani) file changed; no ELF rebuild trigger.']
(E/'NFQ_SLICE_D.md').write_text('\n'.join(text)+'\n')
text=['# D union Q union S coverage','',f'**{len(rows)-len(outside)}/587 rows covered; {len(outside)} outside.** No claim of exhaustive coverage beyond the canonical inventory.', '', 'Function membership matches the original VERTICAL-SLICES semantics. NFQ_COVERAGE.json provides all 587 assignments and per-transaction shortest canonical paths. TX1 entry reaches 345/345 rows; TX2 entry reaches 234/242. Eight TX2 rows lack a TX2-specific path. Six have slice membership through the canonical union; two remain outside all slices. Membership does not prove TX2 reachability or native closure.', '', '| Outside row | Function | Reason |','|---|---|---|']
text += [f'| {r["row"]} | `{r["function"]}` | {r["reason"]} |' for r in outside]
text+=['','Frozen `first_decoded` ends in `.map_err(error)`, but canonical_callees lists only tx1 and observer. This is an inventory callback omission. Add a separately reviewed callback edge in the authoritative inventory to cover error; this job does not modify that inventory. Covered rows lacking a TX2 path are listed below. The union paths can cross transaction inventory records; they establish canonical dependency coverage, not physical same-run reachability.','']
text += [f'- {r["row"]}: `{r["function"]}`' for r in coverage if r['slices'] and r['frozen_call_path'] is None]
(E/'NFQ_COVERAGE.md').write_text('\n'.join(text)+'\n')
print(json.dumps(dict(functions=len(D),edges=len(edges),rows=len(dr),statuses=dict(collections.Counter(r['composed_status'] for r in dr)),outside=[r['row'] for r in outside])))
