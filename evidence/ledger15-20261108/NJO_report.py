from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent

def report(ledger,resources):
 rows=ledger['rows'];parts={'b':[r for r in rows if r['function'].startswith('programs/')],'c':[r for r in rows if r['function'].startswith('crates/')]};assert[len(parts[g])for g in ['b','c']]==[53,546]
 out='# NJO physical association distances\n\nTarget not yet established. (ao)(3) owner/graph distances, preserving the same conservative 599-row NIU inventory and all original caller/trust/source-to-ELF qualifications. Counts do not assert runtime/ELF identity or discharge the headline hypotheses.\n\n| Hypothesis | Rows | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
 counts={}
 for g,rs in parts.items():
  c=collections.Counter(r['status']for r in rs);counts[g]=dict(c);out+=f"| (ao)(3)({g}) | {len(rs)} | {c['CLOSED']} | {c['OPEN']} | {c['QUALIFIED']} |\n"
 # BFS on actual canonical call edges, independently inside each TX cohort.
 paths=[]
 for tx,start,target in [('TX1','330','094'),('TX2','213','115')]:
  rs=[r for r in rows if r['row'].startswith(tx+':')];byfun={r['function']:r for r in rs};byrow={r['row']:r for r in rs};sr=byrow[tx+':'+start];tr=byrow[tx+':'+target];queue=collections.deque([[sr['function']]]);path=None
  while queue:
   p=queue.popleft()
   if p[-1]==tr['function']:path=p;break
   for c in byfun[p[-1]]['canonical_callees']:
    if c in byfun and c not in p:queue.append(p+[c])
  assert path
  packet=[dict(row=byfun[f]['row'],function=f,status=byfun[f]['status'])for f in path];paths.append(dict(transaction=tx,edges=len(path)-1,path=packet,remaining_open=[r['row']for r in packet if r['status']=='OPEN']))
 out+='\n## Shortest actual spine paths\n\nBFS uses the retained canonical callee graph within the transaction cohort, includes CLOSED prerequisites/endpoints, and removes no conservative edge. No unrelated leaf holds a unit.\n'
 for p in paths:
  out+='\n'+p['transaction']+': '+' → '.join(r['row']+' '+r['function'].split('::')[-1]+' ['+r['status']+']'for r in p['path'])+'.\n\nRemaining OPEN on this path: '+', '.join(p['remaining_open'])+f" ({len(p['remaining_open'])} rows, {p['edges']} call edges).\n"
 out+='\nTX2 finish_relation is CLOSED conditionally on the SAME-call NIG_FinishInput.Domain; tx2_common remains OPEN and must prove that domain on its actual View/Prepared/Accumulator/proof. Closed nested pair/finish does not close the upstream driver. TX1:142 remains OPEN independently; the other NIX leaf packets do not close op9/verify_observed.\n'
 for g,rs in parts.items():
  out+=f'\n## (ao)(3)({g}) complete row inventory\n\n| Row | Status | Function | Canonical owner |\n|---|---|---|---|\n'
  for r in rs:out+=f"| {r['row']} | {r['status']} | {r['function']} | {r['owner_module']} |\n"
 pool=(E.parent/'ledger14-20261108/NJK_PHYSICAL.md').read_text().split('## (ao)(3)(d): named Pool obligations',1)[1]
 pool=pool.split('\n\nNIZ latest support:',1)[0]
 pool=pool.replace('NIO supplies local support, zero actual-site certificates.','NIO and NIZ supply local support, zero complete actual-site certificates.').replace('NIO inspection','NIO/NIZ inspection').replace('NIU documents','NJK documents').replace('NIU_PHYSICAL','NJO_PHYSICAL')
 out+='\n## (ao)(3)(d): named Pool obligations'+pool+'\n\nNIZ latest support: all four held CPI/callback units OPEN; 0/13 complete exclusive-guard owners; zero production Pool-consumer rows CLOSED. K086 production reachability/exclusion remains unproved. Ruling (at) adds NO PDA value row: op38 reply remains quantified; native seed/program-id/reply/status/frame forwarding is still required. No trust row changes in NJO.\n'
 (E/'NJO_PHYSICAL.md').write_text(out)
 old=json.loads((E.parent/'ledger14-20261108/NJK_PHYSICAL.json').read_text());old.update(b=counts,shortest_spines=paths);(E/'NJO_PHYSICAL.json').write_text(json.dumps(old,indent=1)+'\n')
 plan='''# NJO plan status

Target not yet established. Ledger15 gate PASS:463 CLOSED /0 QUALIFIED /136 OPEN of599, a25-row increase over NJK438/161. NJE:24 occurrences (TX1:118-126,128,302-304,307; TX2:084-092,094); NJB:TX1:268. Each TX1/TX2 occurrence was checked against its OWN complete obligation and caller clauses. No already CLOSED occurrence counted. NJG/NJA and all other support-only packets get zero additional credit.

Helper own domains do not discharge the multiproof unit. All original clauses remain verbatim at each credited row, and20 explicit occurrence-specific unit-domain caller clauses are recorded on verify_in_place TX1:127/TX2:093, still OPEN. Their different multiproof/U09 requirements, exact slots, padding, sorting/deduplication, SAME Prepared/proof and chronological query/error prefixes remain required. No96-byte native node domain is accepted for these parents.

(aq)(2): root hypotheses inventoried in NJO_CANDIDATE_REVIEW and printed in L002/L039. Reviewed native cuts have emitted SAME replies installed; all child-domain/value obligations are discharged internally. Own canonical/index/typed-input domains remain caller-established. Runtime hashv is the already admitted runtime realization slot, exact slices and reply transport only, not a free arbitrary Ops dictionary or a proof of SHA value. NIG_FinishInput.Domain on inherited finish rows remains. (ar)/(as): no probe credit, entry closes last. (at): no PDA value row; op38 remains quantified; NJK observer provenance unchanged. (au): no arbitrary Ops/Boundaries root is admitted; pinned Aeneas/library adapters and safe std semantics retain their existing scope. Copy patch/control and K-2/K-3 quarantine rules remain binding. This cycle adds no ruling or trust row.

K086 RETAINED liveness/abort finding. Production reachability/exclusion UNPROVED. Owner decision point(aj)(a) PENDING; Pool-inside-game settlement recommendation unchanged. RuntimeCpiReadonlyEntry7 PENDING/unused. RuntimeEntrypointAdmission-Pool remains only the seven initial-entry fields; no CPI frame or success inferred. RuntimePersistence data-only item retained. Existing trust rows are byte-for-data unchanged. P6/D188 option-A native semantic transport is RECLASSIFICATION, never removal.

Post-admission physical distance: (ao)(3)(b)38/53 CLOSED,15 OPEN; (c)425/546 CLOSED,121 OPEN. TX1 shortest entry-to-tx1 spine has6 OPEN rows; TX2 entry-to-finish spine has6 OPEN ancestors and a conditionally CLOSED finish endpoint. All production Pool obligations by name and exact remaining paths appear in NJO_PHYSICAL.md. Three inherited Pool helper rows do not form a production inventory.

Frozen3, headline AspisR1.RPx_Deployed.deployed, L154 parameter, narrowed D188,100-bit PER-ATTEMPT soundness, privacy and two transactions are unchanged. Digest/error slots op43/op44. No headline hypothesis discharged. Native entry/op9/TX2 common/production Pool association, L187 cold release replay and L188 final source-to-ELF/extraction audit remain. The three ELF pins are inherited; no shipped source changed and no rebuild trigger fired.
'''
 (E/'NJO_PLAN_STATUS.md').write_text(plan)
 rem='# NJO remaining obligations\n\nTarget not yet established.40/40 serial Lean/link/audit scopes consumed;0 Kani/0 extraction. All25 submitted occurrences admitted only after the combined gate. No unresolved candidate is hidden, and no new candidate outside this job is promoted.\n\n| Row | Function | Exact remaining association |\n|---|---|---|\n'
 for tx in ['TX1','TX2']:
  byfun={r['function']:r for r in rows if r['transaction']==tx}
  for r in rows:
   if r['status']!='OPEN' or r['transaction']!=tx:continue
   deps=[byfun[d]['row']for d in r['canonical_callees']if d in byfun and byfun[d]['status']=='OPEN']
   why='SAME native/source inputs, full Result/post/frame, ordered effects and every original caller-domain clause.'
   if deps:why+=' OPEN conservative dependencies: '+', '.join(deps)+'.'
   if r['row'] in ['TX1:127','TX2:093']:why='Complete Bool/both mutable arrays/chronological digest-query and abort-prefix native root;96-byte node restriction is stronger than actual callers. Selected-window/KMX frame composition and full caller unit-domain derivation remain. All original and NJO explicit unit caller clauses retained.'
   if r['row']=='TX1:142':why='Missing concrete installed positive native dispatch root consuming NIX_DispatchCut.cut; arbitrary Boundaries B and child endpoint premises remain prohibited by(aq)(2)/(au)(5). This includes Lean-only composition, not a blanket need for new Kani.'
   if r['row']=='TX1:306':why='Actual frozen permutation controller/std-zip/deployed no-op callback-to22-witness association and native controls remain; NJE L095 round witnesses are support only.'
   if r['row']=='TX1:305':why='Actual permutation dependency TX1:306 plus SAME-state native compression caller/output association; NJE L096 seed/tweak/result composition is support only.'
   rem+=f"| {r['row']} | {r['function']} | {why} |\n"
 rem+='''
## Job members

NJE20 multiproof helper occurrences: complete own-carrier root/cut law and SAME-callee domains admitted per occurrence. TX1:127/TX2:093 remain OPEN on the full native/unit obligation; helper closure cannot establish the full mutable driver. Their missing native window/control certificates need Kani in the owning job; the corresponding frame/induction composition remains Lean-only.
NJE4 field/linear occurrences: reviewed cuts, full scalar or mutable state results, field/reducer domains and emitted laws admitted; no field multiplication in Kani. No job-local Lean obligation remains for these4 rows. Permutation/compression support is not a submitted candidate and remains OPEN above, with native and Lean association obligations distinguished.
NJB TX1:268: unconditional complete semantic_public constructor on every typed immutable statement, SAME borrowed public/transition identity. No child/success/endpoint/Run premise; original enclosing public-codec and ABI/source-to-ELF caller clauses retained. No other NJB row submitted or promoted.
NJG and NJA: support-only combined imports and all roots replayed; no candidate promotion. NJG's complete observed/driver association remains with its owner; no arbitrary Ops at a root admitted. Previously rejected TX1:142 remains OPEN independently.

All136 OPEN occurrences are enumerated above; full exact obligations in NJO_LEDGER.json.xz supersede no clause. This job authors no replacement for a missing native/Lean packet outside the25 reviewed candidates. No claim that every OPEN item needs Kani: unassembled substitutions/domain/frame/induction obligations remain Lean-only; native stage/callback/window associations and controls require Kani in their owning lanes, with extraction as separately authorized.

Production Pool: named NIB-P1..P4, POOL.prefix_to_cpi, production POOL.read_to_settlement, all4 held CPI/callback sites and13 exclusive-guard owners remain OPEN; exact source names are NJO_PHYSICAL.md. Authoritative finite production-root inventory and all21 accessor-site associations remain missing. K086 production reachability/exclusion unproved. Owner(aj)(a) pending. RuntimeCpiReadonlyEntry7 unused; no PDA value row. No trust row changed.

Next deliverables: full-domain verify_in_place mutable/query-prefix root; actual permutation/compression association; concrete NIX dispatch root; bottom-up actual TX1/TX2 driver and entry packets; production Pool continuation and final release gates. L187 cold release replay/L188 final artifact audit remain. Target not yet established.
'''
 (E/'NJO_REMAINING.md').write_text(rem)
