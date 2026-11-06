from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;P=E.parent/'ledger15-20261108'
def live(r):
 rid=r['row'];f=r['function']
 if rid in ['TX1:066','TX1:067','TX1:068','TX1:069','TX1:070','TX1:129']:return 'NJT_ claims-queryscan'
 if rid in ['TX2:152','TX2:153','TX2:201','TX2:203']:return 'NJQ_ tx2-decoders2'
 if rid in ['TX1:127','TX2:093']:return 'NJV_ multiproof4'
 if f.split('::')[-1]in['batch_key_at','batch_keys','batch_leaf','batch_merkle','batch_merkle_values','batch_tree','same_batch_index','same_batch_leaf','slot','sort_batch_keys']:return 'NJS_ batch-merkle (cluster overlap; exact ownership to lead)'
 if rid in ['TX2:064','TX2:065','TX2:099','TX2:100','TX2:102','TX2:105','TX2:106','TX2:107','TX2:121','TX2:122','TX2:124','TX2:126']:return 'NJU_ tx2-native8 (cluster overlap; exact ownership to lead)'
 if rid in ['TX1:136','TX1:256']:return 'Next post-NJL job under (av)(4); no named live owner in brief'
 return 'No named live owner in brief'
def residue(r):
 rid=r['row']
 if rid in ['TX1:127','TX2:093']:return 'Full-domain native invocation/both mutable buffers/chronological digest log and abort prefixes plus Lean frame/induction and final cohort endpoint. NJP window support is not the completed root; exact original unit/own domains retained.'
 if rid=='TX1:129':return 'Borrow-minimal changed reference under (av), emitted source, native whole-owned-payload/carrier/allocator/error/cleanup association. NJM E001 failed, no body credit; NJT owns continuation.'
 if rid=='TX1:136':return 'Compose claims129 and terminal256 only after both roots close; SAME source-order/native reply/effects/frame join remains.'
 if rid=='TX1:256':return 'Complete terminal parent source-order/cohort/native result association on actual canonical parsed Claims; NJL children alone do not close it. Ownership corrected by(av)(4).'
 if rid=='TX2:065':return 'SAME native parent assembly, Merkle certificate, complete finish raw-window case split. (aw) adds115 complementary Err/abort child law, not NoBad/persistence/history hypothesis. Lean-only substitution/domain composition remains alongside native stage cuts.'
 if rid in ['TX2:152','TX2:153','TX2:201','TX2:203']:return 'Missing emitted decoder body from NJI-F1 plus native/source parser/record/error/abort association. NJQ live repair; master153 additionally needs boundary149. Existing native support cannot replace emission.'
 if rid=='TX1:224':return 'NJL WindowInvocation same-packet join sketch remains UNCOMPILED; complete8step powers/cache/write frame support exists. Lean-only join14tail/cohort association remains; no blanket new-Kani requirement.'
 if rid in ['TX1:234','TX1:235','TX1:246']:return 'NJL group/iteration/Some native support exists; arithmetic/domain/frame/finite induction and actual cohort/root composition remain Lean-only in part. Do not book support as row closure.'
 return 'Exact original obligation remains in ledger: SAME native/source inputs, full Result/post/frame and chronological effects; all caller domains/typed conservative alternatives must be discharged. Native cuts/controls if absent need Kani in owner lane; existing-cut substitution, domain, frame and induction work can remain Lean-only.'
def report(ledger,resources):
 rows=ledger['rows'];parts={g:[r for r in rows if r['function'].startswith(prefix)]for g,prefix in [('b','programs/'),('c','crates/')]};assert[len(parts[g])for g in['b','c']]==[53,546]
 counts={g:dict(collections.Counter(r['status']for r in rs))for g,rs in parts.items()}
 out='# NJW physical association distances\n\nTarget not yet established. Recomputed (ao)(3)(b) entry and(c) native-forest counts in the unchanged599-function inventory after the gated admissions. These conditional source association distances do not discharge runtime/source-to-ELF or headline premises.\n\n| Part | Total | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
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
 out+='\n## Shortest actual spine paths\n\nBFS uses the actual retained canonical call edges within each transaction cohort; no conservative edge pruned.\n'
 for p in paths:out+='\n'+p['transaction']+': '+' → '.join(r['row']+' '+r['function'].split('::')[-1]+' ['+r['status']+']'for r in p['path'])+f".\n\nOPEN distance {len(p['remaining_open'])}; {p['edges']} call edges. OPEN rows: "+', '.join(p['remaining_open'])+'.\n'
 out+='\nTX2:115 finish_relation stays CLOSED exactly on its SAME-call NIG_FinishInput.Domain. NEW OPEN child supplement NJW-aw-TX2:115-off-domain must cover current-byte window failures with SAME Err/abort and ordered prefixes under(aw)(3). It is tracked separately, outside the599 function occurrences; no row count or trust row is changed by inventing a600th occurrence. TX2:065 must use the two branches without a history/NoBad/persistence premise.\n'
 grouped=collections.defaultdict(list)
 for r in rows:
  if r['status']=='OPEN':grouped[r['function'].split('::')[0]].append(r)
 out+='\n## OPEN rows grouped by frozen source file\n\nLive owners are the five jobs named in the brief; cluster overlap is marked where the brief gives no exact row list. No sibling worktree was accessed.\n'
 for file,rs in sorted(grouped.items()):
  out+='\n### '+file+'\n\n| Row | Function | Live owner / routing |\n|---|---|---|\n'
  for r in rs:out+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {live(r)} |\n"
 pool=(P/'NJO_PHYSICAL.md').read_text().split('## (ao)(3)(d): named Pool obligations',1)[1]
 out+='\n## (ao)(3)(d): named Pool obligations'+pool.replace('No trust row changes in NJO.','No trust row changes in NJW.').replace('NJO_PHYSICAL','NJW_PHYSICAL')
 out+='\nPool statuses inherited and re-listed by name; none of NJI’s typed policy/master/registry validators creates a production Pool consumer or actual CPI continuation certificate. K086 production reachability/exclusion remains unproved; owner(aj)(a) PENDING.\n'
 (E/'NJW_PHYSICAL.md').write_text(out)
 old=json.loads((P/'NJO_PHYSICAL.json').read_text());old.update(entry_native_counts=counts,shortest_spines=paths,open_by_source={k:[dict(row=r['row'],function=r['function'],live_owner=live(r))for r in rs]for k,rs in grouped.items()},supplemental_child_obligations=ledger['supplemental_child_obligations']);old['b']=counts;(E/'NJW_PHYSICAL.json').write_text(json.dumps(old,indent=1)+'\n')
 plan='''# NJW plan status

Target not yet established. Ledger16 ninth all-slices gate PASS:484 CLOSED /0 QUALIFIED /115 OPEN of599, versus NJO463/136. Exactly21 fresh occurrences: NJI4, NJM3, NJP2, NJL12; no ledger13/14 delta reused or double count. No support-only NJR/NJN or outside row promoted.

Complete obligations including every original caller/unit clause retained. NJW_PARENT_CLAUSES.json explicitly records42 own-domain/unit-context requirements at actual parents; internal domain uses have named root discharges, upstream provenance remains OPEN. No extra successful child/endpoint/Run/arbitrary Ops hypothesis. NJM rounds’ sole Prop input is exactly the reviewed K016–019(ai)(5) transcription. All four NJI candidate bodies are actually emitted, used by the root’s raw definition chain and nonopaque; NJI-F1’s four other missing decoder bodies remain OPEN. Canonical NGK/NIU/NJB/NIX/NJO owners are unchanged.

(av) APPLIED: references are borrow-minimal; after NJL, TX1:256 terminal_qm31 and136 verify_finish belong to the next launched consuming job. NJT owns129 and QueryScan066–070. No claims/terminal/finish row promoted here.
(aw) APPLIED:115 stays CLOSED as stated on SAME-call NIG_FinishInput.Domain. NEW OPEN child supplement covers off-window Err/abort with identical ordered prefixes; TX2:065 must case-split current bytes, without NoBad/history/persistence or success premise. Supplemental obligation is tracked outside599, not a new game/trust premise. NJR support alone does not close tx2_common.

K086 RETAINED liveness/abort finding; production reachability/exclusion UNPROVED. Owner decision point(aj)(a) PENDING. RuntimeCpiReadonlyEntry7 unused. Existing trust rows byte-for-data unchanged. RuntimePersistence remains data-only; Pool runtime entry item remains only seven initial-entry fields, not CPI success/frame. P6/D188 option-A semantic transport is RECLASSIFICATION, never removal. No PDA value row; op38 quantified; coherent digest/error op43/op44.

Physical distance: (ao)(3)(b)38/53 CLOSED15 OPEN; (c)446/546 CLOSED100 OPEN. Both shortest transaction spines retain6 OPEN ancestors/rows (TX2 has a conditionally CLOSED115 endpoint plus its new supplemental law). Exact paths, all115 OPEN rows grouped by source/live ownership and named Pool obligations are NJW_PHYSICAL.md.

Frozen3, AspisR1.RPx_Deployed.deployed headline, L154 parameter, narrowed D188,100-bit PER-ATTEMPT soundness, privacy and two transactions unchanged. No headline hypothesis discharged. Native entry/op9/TX2 common/production Pool association, L187 cold release replay and L188 artifact/extraction audit remain. No shipped source change or ELF rebuild trigger; the three ELF hashes are inherited pins only.
'''
 (E/'NJW_PLAN_STATUS.md').write_text(plan)
 rem='# NJW remaining obligations\n\nTarget not yet established.40/40 serial Lean/link/audit scopes used;0 Kani/0 extraction. All21 candidates admitted only after the full gate. The115 conservative OPEN occurrences are listed below. No claim that every row requires Kani: native cut/control gaps and Lean-only domain/frame/induction/assembly gaps are distinguished.\n'
 for file,rs in sorted(grouped.items()):
  rem+='\n## '+file+'\n\n| Row | Member | Remaining obligation | Live routing |\n|---|---|---|---|\n'
  for r in rs:
   deps=[q['row']for q in rows if q['transaction']==r['transaction']and q['status']=='OPEN'and q['function']in r['canonical_callees']]
   rem+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {residue(r)}"+(' OPEN conservative children: '+', '.join(deps)+'.'if deps else'')+f" | {live(r)} |\n"
 rem+='\n## Additional child and Pool obligations\n\nNEW(aw)(3): NJW-aw-TX2:115-off-domain OPEN; same actual arbitrary-word native cut and matched failure/abort association required, plus Lean domain-complement/control/order composition.115 remains conditionally CLOSED on its original Domain. This is an extra child law, not another numbered function occurrence or new game premise. NJU live TX2-native8 overlaps; exact supplement ownership remains with lead.\n\nAll named production Pool NIB-P1..P4, prefix/read-to-settlement, four held CPI/callback sites,13 exclusive guard owners and21 actual accessor-site associations remain OPEN; NJW_PHYSICAL.md retains their exact names/status. No authoritative finite production inventory or complete Pool continuation follows from the verifier inventory. K086 production reachability/exclusion unproved; (aj)(a) pending.\n\nNext deliverables: consume live NJQ/NJS/NJT/NJU/NJV packets bottom-up under(aq); complement115 per(aw); compile NJL224 same-packet join and finish tail/cohort; compose remaining terminal/claims/prepare/op9 and actual entry/source-to-ELF/Pool continuation. No unchanged full regression or unreviewed horizontal WIP earns credit. Budget exhaustion, not Kani exhaustion, ends this ledger job.\n'
 (E/'NJW_REMAINING.md').write_text(rem)
