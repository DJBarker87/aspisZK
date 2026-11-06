from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent

def report(ledger,resources):
 rows=ledger['rows'];parts={'b':[r for r in rows if r['function'].startswith('programs/')],'c':[r for r in rows if r['function'].startswith('crates/')]};assert[len(parts[g])for g in ['b','c']]==[53,546]
 out='# NJK physical association distances\n\nTarget not yet established. (ao)(3) owner/graph distances, preserving the same conservative 599-row NIU inventory and all original caller/trust/source-to-ELF qualifications. Counts do not assert runtime/ELF identity or discharge the headline hypotheses.\n\n| Hypothesis | Rows | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
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
 pool=(E.parent/'ledger13-20261107/NIU_PHYSICAL.md').read_text().split('## (ao)(3)(d): named Pool obligations',1)[1]
 pool=pool.replace('NIO supplies local support, zero actual-site certificates.','NIO and NIZ supply local support, zero complete actual-site certificates.').replace('NIO inspection','NIO/NIZ inspection').replace('NIU documents','NJK documents').replace('NIU_PHYSICAL','NJK_PHYSICAL')
 out+='\n## (ao)(3)(d): named Pool obligations'+pool+'\n\nNIZ latest support: all four held CPI/callback units OPEN; 0/13 complete exclusive-guard owners; zero production Pool-consumer rows CLOSED. K086 production reachability/exclusion remains unproved. Ruling (at) adds NO PDA value row: op38 reply remains quantified; native seed/program-id/reply/status/frame forwarding is still required. No trust row changes in NJK.\n'
 (E/'NJK_PHYSICAL.md').write_text(out)
 old=json.loads((E.parent/'ledger13-20261107/NIU_PHYSICAL.json').read_text());old.update(b=counts,shortest_spines=paths);(E/'NJK_PHYSICAL.json').write_text(json.dumps(old,indent=1)+'\n')
 plan=(E.parent/'ledger13-20261107/NIU_PLAN_STATUS.md').read_text()
 plan='# NJK plan status\n\nTarget not yet established. Authoritative current refresh is NJK; inherited NIU details follow after the explicit current delta. No trust-row change.\n\n'+'''Six admitted rows: TX2:129/115 (NJF), TX1:156/215 (NIX), TX1:329 and TX2:212 (NJH, CLOSED under(as)(3)). 432/167 becomes438 CLOSED/161 OPEN of599, zero QUALIFIED. TX1:142 REJECTED: NIX_ValidatedCut.source arbitrary Boundaries B and missing complete positive dispatch-cut instantiation, (aq)(2)/(au)(5). Supporting NIW/NIY/NIZ/NIV/NJA/NJD/NJC imports do not promote rows. TX1:215 is counted once, independent of NJB's list.

(aq): all admitted native child clauses discharged internally at SAME arguments; retained NIG_FinishInput.Domain and reviewed PairPort cut explicitly remain. (ar): no probe count is closure. (as): entry closes last; the two observer leaves use the explicit Lean-only constant-body route. (at): NJH-F1 provenance checked against canonical AdapterRwModel, raw Aeneas observer and byte-identical frozen program lib; no PDA row ADDED. (au): arbitrary Ops/Boundaries root assumptions are not admitted; no new Std child-row obstruction invented.

K086 RETAINED liveness/abort finding; production reachability/exclusion UNPROVED. Owner decision point(aj)(a) PENDING. RuntimeCpiReadonlyEntry7 PENDING/unused. All existing trust rows remain byte-for-data unchanged. P6/D188 option-A native semantic transport is RECLASSIFICATION, never removal. Initial Pool RuntimeEntrypointAdmission-Pool supplies only the seven existing entry fields, no CPI frame/success. RuntimePersistence data-only item unchanged.

Post-admission physical distances: (b)38/53 CLOSED,15 OPEN; (c)400/546 CLOSED,146 OPEN. Production Pool(d) still has no authoritative complete finite numbered inventory: all named NIB-P1..P4, production prefix/read/settlement, four held CPI/callback sites and13 exclusive-guard owners remain production OPEN. Three inherited helper rows are not production closure. Exact names/statuses and shortest spines are NJK_PHYSICAL.md.

Frozen3, headline AspisR1.RPx_Deployed.deployed, L154 parameter and narrowed D188 remain. 100-bit PER-ATTEMPT soundness, privacy and two transactions unchanged. No grinding/work-normalized credit. Native entry/op9/TX2 common/Pool producer association, L187 cold release replay and L188 final native/source-to-ELF audit remain. No discharged headline hypotheses and no established security target.

## Historical NIU plan, retained as history (counts superseded above)

'''+plan
 (E/'NJK_PLAN_STATUS.md').write_text(plan)
 rem='# NJK remaining obligations\n\nTarget not yet established. 40/40 serial Lean/link/audit scopes used, 0 Kani/0 extraction. Every job candidate reviewed and every required root audited; no remaining in-scope candidate could be promoted without its exact missing packet. This is not an early stop. Existing arbitrary dictionary/child-success premises are never repaired by declaration renaming.\n\n| Exact row | Function | Exact remaining association |\n|---|---|---|\n'
 byfun={r['function']:r for r in rows}
 for r in rows:
  if r['status']!='OPEN':continue
  deps=[byfun[d]['row']for d in r['canonical_callees']if d in byfun and byfun[d]['status']=='OPEN']
  reason='Actual native/source SAME-input complete Result/effect/frame and caller domains.'
  if deps:reason+=' OPEN conservative children: '+', '.join(deps)+'.'
  if r['row']=='TX1:142':reason='Exact missing positive native dispatch root: instantiate concrete circle dictionary and consume NIX_DispatchCut.cut, discharging every child clause internally. NIX_ValidatedCut.source and NIX_DispatchRun.returned retain prohibited arbitrary B/endpoint premise at the cited boundary. Lean composition remains; no new Kani asserted necessary.'
  rem+=f"| {r['row']} | {r['function']} | {reason} |\n"
 rem+='''
## Member-by-member job disposition

NJF TX2:129/115: admitted only within the SAME complete invocation capsule and retained Domain/PairPort caller clauses. No job-local Lean obligation remains. Upstream tx2_common/entry native packets and their domain derivation remain in their own rows, not charged as new caller premises here.
NIX TX1:156/215: complete packet/cut and canonical operand derivations admitted. copy_residual counted once. No job-local Lean obligation remains for these two rows.
NIX TX1:142: OPEN for the exact missing Lean positive invocation root above. This is a Lean-only remaining obligation and is explicitly not characterized as requiring Kani. The gate audits the submitted packet and rejects it; NJK authors no replacement positive root after the already fixed combined gate.
NJH TX1:329/TX2:212: admitted under(as)(3) after canonical emission/frozen-body provenance check. No native pointer verdict or new runtime premise.

Supporting NIW,NIY,NIZ,NIV,NJA,NJD,NJC: read-only combined imports and all their roots replayed, zero additional candidates/promotions. Their own remaining inventories stay authoritative. NJC's child-result candidates are supporting emitted facts, not additional native row candidates in this JOB.

All161 remaining OPEN occurrences are named above. Complete original obligations are retained in NJK_LEDGER.json.xz; abbreviated descriptions never replace them. Entry rows require actual native stage cuts on child-complete domains; TX1 driver requires complete op9/observed/finish and allocator/native loop packets; TX2 common requires complete same-resume/query/native cut instantiation. Missing native cuts need Kani in their owning jobs, while any listed unassembled Lean substitutions remain Lean-only; no blanket claim that all OPEN rows require new Kani.

Production Pool: NIB-P1/P2/P3/P4, POOL.prefix_to_cpi and production read_to_settlement remain OPEN; each of four held sites and13 exclusive owners is named in NJK_PHYSICAL.md. Full caller/CPI/source/metadata/token/cleanup association and an authoritative production-root inventory remain. K086 production reachability/exclusion unproved; owner(aj)(a) pending. RuntimeCpiReadonlyEntry7 unused; PDA value row NOT added; op38 native byte/reply/status/frame forwarding remains. No trust row changed.

L187 cold frozen-release replay and L188 final artifact/extraction audit remain. No 100-bit per-attempt soundness/privacy/two-transaction headline established. Next action: submit the missing concrete NIX dispatch invocation theorem; close actual TX1/TX2 driver packets bottom-up; then entry, then production Pool and final release gates.
'''
 (E/'NJK_REMAINING.md').write_text(rem)
