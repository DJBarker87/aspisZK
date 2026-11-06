from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;P=E.parent/'ledger16-20261108'
def live(r):
 rid=r['row'];f=r['function']
 if rid in ['TX2:065','TX2:124']:return 'NJU_ tx2-native8'
 if rid in ['TX1:129','TX1:069','TX1:136']:return 'NKA_ claims2'
 if rid in ['TX1:081','TX1:082','TX1:083','TX1:084','TX2:053','TX2:054','TX2:055']:return 'NKB_ batch-merkle2'
 if rid in ['TX1:201','TX1:202','TX1:203','TX1:204']or f.startswith('crates/aspis-r1-cost-probe/src/verifier.rs::'):return 'NJZ_ verifier-weights'
 if rid=='TX1:256'or 'terminal.rs::'in f:return 'NJX_ terminal3 (terminal cluster; precise unlisted row assignment to lead)'
 return 'No named live owner in brief; S2 lead routing'
def report(ledger,resources):
 rows=ledger['rows'];parts={g:[r for r in rows if r['function'].startswith(prefix)]for g,prefix in [('b','programs/'),('c','crates/')]};assert[len(parts[g])for g in['b','c']]==[53,546]
 counts={g:dict(collections.Counter(r['status']for r in rs))for g,rs in parts.items()}
 out='# NKC physical association distances\n\nTarget not yet established. Recomputed after this job’s gated admissions over the retained599-function inventory. Conditional native/source association is separate from runtime/source-to-ELF and headline obligations.\n\n| Part | Total | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
 for g,rs in parts.items():
  c=counts[g];out+=f"| (ao)(3)({g}) | {len(rs)} | {c.get('CLOSED',0)} | {c.get('OPEN',0)} | {c.get('QUALIFIED',0)} |\n"
 paths=[]
 for tx,start,target in [('TX1','330','094'),('TX2','213','115')]:
  rs=[r for r in rows if r['row'].startswith(tx+':')];byfun={r['function']:r for r in rs};byrow={r['row']:r for r in rs};queue=collections.deque([[byrow[tx+':'+start]['function']]]);found=None
  while queue:
   p=queue.popleft()
   if p[-1]==byrow[tx+':'+target]['function']:found=p;break
   for c in byfun[p[-1]]['canonical_callees']:
    if c in byfun and c not in p:queue.append(p+[c])
  assert found
  packet=[dict(row=byfun[f]['row'],function=f,status=byfun[f]['status'],owner=byfun[f]['owner_module'])for f in found];paths.append(dict(transaction=tx,edges=len(found)-1,path=packet,remaining_open=[r['row']for r in packet if r['status']=='OPEN']))
 out+='\n## Shortest spine paths\n\nBFS over retained canonical call edges in each transaction; reclassified spurious-by-name edge069→202 remains visible and is not deleted.\n'
 for p in paths:out+='\n'+p['transaction']+': '+' → '.join(r['row']+' '+r['function'].split('::')[-1]+' ['+r['status']+']'for r in p['path'])+f".\n\nOPEN distance {len(p['remaining_open'])}; {p['edges']} call edges.\n"
 out+='\nTX2:115 remains CLOSED as stated on SAME-call NIG_FinishInput.Domain. NEW OPEN(aw) supplement NJW-aw-TX2:115-off-domain remains outside599: SAME-current-byte off-window Err/abort and ordered-prefix law; no NoBad/history/persistence/accepted-finish premise.\n'
 grouped=collections.defaultdict(list)
 for r in rows:
  if r['status']=='OPEN':grouped[r['function'].split('::')[0]].append(r)
 out+='\n## OPEN rows by source file and live owner\n'
 for file,rs in sorted(grouped.items()):
  out+='\n### '+file+'\n\n| Row | Function | Live routing |\n|---|---|---|\n'
  for r in rs:out+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {live(r)} |\n"
 pool=(P/'NJW_PHYSICAL.md').read_text().split('## (ao)(3)(d): named Pool obligations',1)[1]
 out+='\n## (ao)(3)(d): named Pool obligations'+pool.split('Pool statuses inherited and re-listed by name;',1)[0].replace('NJW_PHYSICAL','NKC_PHYSICAL').replace('No trust row changes in NJW.','No runtime or cryptographic trust row changes in NKC.')
 out+='\nNJY-B1 retained: raw decoder rows149/152/153/201/203 do not close Box/ProgramError wrapper consumers48/49 or production Pool joins. No authoritative finite production inventory follows. K086 production reachability/exclusion UNPROVED; owner(aj)(a) PENDING.\n'
 (E/'NKC_PHYSICAL.md').write_text(out)
 old=json.loads((P/'NJW_PHYSICAL.json').read_text());old.update(entry_native_counts=counts,shortest_spines=paths,open_by_source={k:[dict(row=r['row'],function=r['function'],live_owner=live(r))for r in rs]for k,rs in grouped.items()},supplemental_child_obligations=ledger['supplemental_child_obligations']);old['b']=counts;(E/'NKC_PHYSICAL.json').write_text(json.dumps(old,indent=1)+'\n')
 plan='''# NKC plan status

Target not yet established. Ledger17 tenth all-slices gate PASS:514 CLOSED /0 QUALIFIED /85 OPEN of599, versus NJW484/115. Exactly30 fresh occurrences: NJS19, NJT4, NJV2, NJY5. No ledger15 delta reused; no support-only or unsubmitted parent promoted.

Complete NJW obligations, named hypotheses, inventory and caller clauses retained. NKC_PARENT_CLAUSES.json records64 exact own-domain/unit-context clauses at actual parents. Internal calls have named roots; upstream provenance remains OPEN. Every root’s complete kernel statement and canonical owner is retained; no arbitrary Ops, success, endpoint or Run root premise admitted. NJV retains both original units, and from_count does NOT infer10 from TX2’s12.

(av) retained borrow-minimal reference rule. (aw) retained TX2:115 off-domain supplement OPEN,115 CLOSED as stated. (ay) applied to NJY raw decoders: all Result/error arms, loop rejection prefixes, full records and record-shape controls reviewed. NJY-B1 wrapper48/49 stays OPEN. (az)(1)069→202 marked spurious-by-name, kept visible; derived QueryScan::default is not incremental_merkle default. (az)(2) claims129 allocator join remains OPEN.

Trust inventory additions ONLY ReviewedTranscription NJY-RT149/152/153/201/203, P6/D188 option-A RECLASSIFICATION, never removal. Existing runtime/cryptographic trust rows unchanged. RuntimePersistence is data-only; Pool entry trust covers only seven initial-entry fields. RuntimeCpiReadonlyEntry7 unused. No PDA value row; op38 quantified; digest/error op43/op44.

K086 RETAINED liveness/abort finding; production reachability/exclusion UNPROVED. Owner decision point(aj)(a) PENDING. Named Pool NIB-P1..P4, prefix/read-to-settlement, four held sites,13 exclusive owners and21 accessor-site associations remain OPEN. Actual entry/op9/TX2 common/Pool association, L187 cold release replay and L188 artifact/extraction audit remain. Frozen3/deployed headline/L154 parameter/narrowed D188/100-bit PER-ATTEMPT/privacy/two transactions unchanged. No headline hypothesis discharged or ELF rebuild trigger.
'''
 (E/'NKC_PLAN_STATUS.md').write_text(plan)
 rem='# NKC remaining obligations\n\nTarget not yet established.40/40 serial Lean/link/audit scopes used;0 Kani/0 extraction. All30 candidates admitted only after the full gate.85 OPEN occurrences follow. No blanket Kani blocker: existing-cut substitution, caller-domain/frame/induction and source composition may proceed Lean-only; missing native cuts/controls require the owning lane’s Kani allowance.\n'
 for file,rs in sorted(grouped.items()):
  rem+='\n## '+file+'\n\n| Row | Member | Remaining obligation | Live routing |\n|---|---|---|---|\n'
  for r in rs:
   deps=[q['row']for q in rows if q['transaction']==r['transaction']and q['status']=='OPEN'and q['function']in r['canonical_callees']]
   if r['row']=='TX1:069':why='Own source/native composition after066/067 CLOSED; edge202 reclassified spurious-by-name under(az), retained visibly; no new child202 proof required for derived QueryScan default.'
   elif r['row']=='TX1:129':why='(az)(2) SAME1392-byte align4 unsafe allocation/carrier/error/cleanup packet; allocator outcome universally quantified, no success-only reserve. Existing emitted/model support remains Lean-only reusable.'
   elif r['row']=='TX2:065':why='Native parent stage cuts/assembly plus current-byte domain case split; CLOSED Merkle children now available. NEW OPEN115 complement needs arbitrary-word native cut/control and Lean abort/order composition.'
   else:why='Complete original obligation retained: SAME input/native/source/full Result/post/frame and chronological effects; discharge actual caller domains. Missing native cut/control is Kani work; existing-cut substitution/domain/frame/induction/cohort joins are Lean-only work.'
   rem+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {why}"+(' OPEN conservative children: '+', '.join(deps)+'.'if deps else'')+f" | {live(r)} |\n"
 rem+='\n## Additional child and Pool obligations\n\n(aw) NJW-aw-TX2:115-off-domain OPEN; exact SAME current-word native cut and failure control/abort mapping, plus Lean complement/order composition.115 remains CLOSED on original Domain. No600th function occurrence. NJY-B1 Box/ProgramError wrapper consumers48/49 remain OPEN.\n\nEvery named Pool obligation and status is retained in NKC_PHYSICAL.md. K086 and(aj)(a) remain unresolved. Next: consume live NJU/NJX/NJZ/NKA/NKB packets bottom-up under(aq), complete actual entry/op9/source-to-ELF/production Pool continuation. No outside candidate earns credit. Budget exhaustion ends this ledger job, not Kani exhaustion.\n'
 (E/'NKC_REMAINING.md').write_text(rem)
