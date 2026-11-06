from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;P=E.parent/'ledger17-20261108'
def live(r):
 rid=r['row']
 if rid in ['TX1:129','TX1:069','TX1:136']:return 'NKA_ claims2'
 if rid in ['TX1:081','TX1:082','TX1:083','TX1:084','TX2:053','TX2:054','TX2:055']:return 'NKB_ batch-merkle2'
 if rid=='TX2:065':return 'NKE_ tx2-native9 (M01 join)'
 if rid in ['TX2:216','TX2:217','TX2:218','TX2:233','TX2:234','TX2:242']:return 'NKF_ tx2-adapters'
 if rid in ['TX1:308','TX1:321','TX1:323','TX1:324']:return 'NKG_ poseidon-state'
 return 'UNOWNED in current brief; S2 lead routing'
def report(ledger,resources):
 rows=ledger['rows'];parts={g:[r for r in rows if r['function'].startswith(prefix)]for g,prefix in [('b','programs/'),('c','crates/')]};assert [len(parts[g])for g in ['b','c']]==[53,546]
 counts={g:dict(collections.Counter(r['status']for r in rs))for g,rs in parts.items()};paths=[]
 out='# NKH physical association distances\n\nTarget not yet established. Recomputed from599 retained function occurrences after the full combined gate admitted28candidate occurrences. These are conditional native/source associations; entry/caller/runtime/source-to-ELF/headline obligations remain.\n\n| Part | Total | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
 for g,rs in parts.items():
  c=counts[g];out+=f"| (ao)(3)({g}) | {len(rs)} | {c.get('CLOSED',0)} | {c.get('OPEN',0)} | {c.get('QUALIFIED',0)} |\n"
 out+='\nEntry(b)38/53 and native forest(c)504/546 CLOSED;15entry and42forest occurrences remain OPEN,57total. No parent or production association is inferred from a helper closure.\n\n## Shortest OPEN spine paths\n\nBFS over the retained canonical call graph. The spurious-by-name069→202 edge remains visible under(az)(1).\n'
 for tx,start,target in [('TX1','330','094'),('TX2','213','115')]:
  rs=[r for r in rows if r['transaction']==tx];byfun={r['function']:r for r in rs};byrow={r['row']:r for r in rs};queue=collections.deque([[byrow[tx+':'+start]['function']]]);found=None
  while queue:
   p=queue.popleft()
   if p[-1]==byrow[tx+':'+target]['function']:found=p;break
   for c in byfun[p[-1]]['canonical_callees']:
    if c in byfun and c not in p:queue.append(p+[c])
  assert found
  packet=[dict(row=byfun[f]['row'],function=f,status=byfun[f]['status'],owner=byfun[f]['owner_module'])for f in found];pp=dict(transaction=tx,edges=len(found)-1,path=packet,remaining_open=[r['row']for r in packet if r['status']=='OPEN']);paths.append(pp)
  out+='\n'+tx+': '+' → '.join(r['row']+' '+r['function'].split('::')[-1]+' ['+r['status']+']'for r in packet)+f".\n\nOPEN distance {len(pp['remaining_open'])}; {pp['edges']} call edges.\n"
 out+='\n(aw) NJW-aw-TX2:115-off-domain CLOSED by the full combined gate: NJU_GeneralFinishRoot.finish/ported establishes a SAME-native-G arbitrary-current-word full Result/prefix law with final length2048 and no NoBad/history/persistence/success premise, and this job completed its all-root gate. It remains outside599. Original115 stays CLOSED as stated;065 remains OPEN.\n'
 grouped=collections.defaultdict(list)
 for r in rows:
  if r['status']=='OPEN':grouped[r['function'].split('::')[0]].append(r)
 out+='\n## OPEN rows grouped by source and live owner\n'
 for f,rs in sorted(grouped.items()):
  out+='\n### '+f+'\n\n| Row | Function | Owning live job |\n|---|---|---|\n'
  for r in rs:out+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {live(r)} |\n"
 unowned=[r['row']for r in rows if r['status']=='OPEN'and live(r).startswith('UNOWNED')]
 out+='\n## Explicit unowned OPEN occurrences\n\n'+', '.join(unowned)+'.\n'
 pool=(P/'NKC_PHYSICAL.md').read_text().split('## (ao)(3)(d): named Pool obligations',1)[1]
 out+='\n## (ao)(3)(d): named Pool obligations'+pool
 out+='\nNKH makes no production Pool promotion or trust-row change. Pool obligations above remain unchanged; 28function occurrences and the off-domain115supplement were admitted. Digest/error are op43/op44 in the coherent SInt2 cohort. RuntimePersistence remains data-only; RuntimeCpiReadonlyEntry7 unused. K086 retained liveness/abort finding; production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING.\n'
 (E/'NKH_PHYSICAL.md').write_text(out)
 old=json.loads((P/'NKC_PHYSICAL.json').read_text());old.update(entry_native_counts=counts,shortest_spines=paths,open_by_source={k:[dict(row=r['row'],function=r['function'],live_owner=live(r))for r in rs]for k,rs in grouped.items()},supplemental_child_obligations=ledger['supplemental_child_obligations'],unowned_open_rows=unowned);old['b']=counts;(E/'NKH_PHYSICAL.json').write_text(json.dumps(old,indent=1)+'\n')
 (E/'NKH_PLAN_STATUS.md').write_text("""# NKH plan status

Target not yet established. Eleventh all-slices composition gate PASS:542 CLOSED /0 QUALIFIED /57 OPEN of599, versus NKC514/85. Exactly28 occurrences admitted: NJZ15/NKD8/NJX5, independently recomputed against NKC; NJU generalized off-domain115 supplement CLOSED outside599. Original115 remains CLOSED as stated; TX2:065/124 remain OPEN.

All original complete obligations, named hypotheses and caller clauses retained.66explicit own-domain/unit-context clauses are recorded at actual parents. Internal domains have named roots; upstream provenance remains OPEN. Full10066root raw audit uses the SAME optimized binary and eight fixtures; standard axioms only, NHC_DecodeModel.decoder_error collector discrepancy retained under(ab')(3). NFX exit0 over16128modules; zero dangling, incompatible/canonical duplicate owners or import mismatches. Complete hypothesis/support-root/matcher-owner prints and selected closure pins retained.

Reader native specialization ONLY N4/16/32 on1768backing U11/S2; generic S1/backing4840 receives no credit. Transcript ONLY deployedSolanaDigest; digest VALUE remains existing runtime trust. echeck every Result/error arm, full returned record and(ay)(4) fidelity controls reviewed. NJX/NJL children use SAME constructed arguments and unchanged NKC roots; canonical JFw matcher owners are unique.

Only ReviewedTranscription additions NJZ-RT189/201/202/203/204, P6/D188 option-A RECLASSIFICATION, never removal. Runtime/cryptographic rows unchanged. RuntimePersistence data-only; initial Pool entry seven fields; RuntimeCpiReadonlyEntry7 unused; op38quantified,digest/error43/44. K086 retained liveness/abort finding, production reachability/exclusion UNPROVED; owner(aj)(a) PENDING. Named production Pool obligations OPEN as before. Frozen3/deployed headline/L154parameter/narrowedD188/100-bitPER-ATTEMPT/privacy/two transactions unchanged.

40/40scopes submitted;39complete receipts and original L025 ENOSPC with unknown child metrics. L026 explicitly resubmitted after lead host repair, retaining5367completed roots and auditing only4699missing roots. L038 runs final two groups serially. All caps6G/8G/swap0/tasks64; optional16G unused.0Kani/0extraction. No shipped source change or ELF rebuild trigger; inherited artifact hashes only. Actual entry/op9/native parent/Pool continuation,L187cold replay,L188artifact/extraction gates remain.
""")
 rem='# NKH remaining obligations\n\nTarget not yet established.40/40scopes submitted,39complete receipts and original host-ENOSPC scope with unavailable metrics;0Kani/0extraction.28candidate occurrences and the off-domain115supplement admitted.57OPEN occurrences remain; full original obligation and caller clauses retained. Budget exhausted. There is Lean-only work remaining. Native cuts/controls below need a future owning lane with Kani; already reviewed-cut substitution/domain/frame/induction and assembly do not.\n'
 for f,rs in sorted(grouped.items()):
  rem+='\n## '+f+'\n\n| Row | Member | Exact remaining boundary / next work | Owner |\n|---|---|---|---|\n'
  for r in rs:
   rid=r['row'];pending={c['row']:c for c in json.loads((E/'NKH_CANDIDATE_REVIEW.json').read_text())['rows']};deps=[q['row']for q in rows if q['transaction']==r['transaction']and q['status']=='OPEN'and q['function']in r['canonical_callees']]
   assert rid not in pending, 'admitted candidate unexpectedly OPEN'
   if rid=='TX1:129':why='(az)(2) SAME1392-byte align4 unsafe allocation/carrier/error/cleanup join, universally quantified allocator outcome. Native allocation/carrier cuts/control need Kani; existing emission/model/domain composition is Lean-only.'
   elif rid=='TX1:069':why='SAME query construction after066/067 CLOSED; derived QueryScan default, edge202 visibly spurious-by-name. Missing native parent cut/control needs Kani; rank/words/finish substitution and domain/frame induction are Lean-only.'
   elif rid=='TX2:065':why='M01 SAME resume/query/flush/finish native parent association and native-log/source assembly;115 off-domain supplement CLOSED by this gate. Native parent cut/control needs Kani if absent; current-word branch/domain/trace substitution is Lean-only. No source-only common theorem promoted.'
   elif rid=='TX2:124':why='Complete resume native parent associations: header/digest/Reader/parsers/owned allocation/cleanup at SAME arguments. Reader/checkpoint candidates CLOSED within their recorded domains. Missing native parent windows/control need Kani; source log-erasure/cohort/domain assembly is Lean-only.'
   elif rid in ['TX1:308','TX1:321','TX1:323','TX1:324']:why='Actual poseidon-state function/source/cohort bridge. Native arbitrary-state/one-step cuts and controls if absent need Kani; symbolic column/domain/loop induction and child substitutions are Lean-only. No field multiplication in Kani.'
   elif r['function'].startswith('programs/') :why='Actual entry/adapter SAME accounts/input/op association, complete Result/error/borrow/drop/ordered effects. Native prefix/carrier/frame controls require Kani where missing; CLOSED child domains, source/trace joins and continuation assembly are Lean-only. No new runtime trust.'
   elif 'batch' in r['function'].lower()or rid=='TX1:084':why='Actual batch/tree invocation, original10-leaf plus TX2 12-leaf units, proof/query/count/padding provenance and all mutable frames. Missing native step/entry/control needs Kani; bound/domain/permutation/frame and generic<=16 induction are Lean-only.'
   else:why='Complete SAME-function native/source/full Result/abort/post/frame/chronological effects packet not admitted. Missing native one-step/call-site cuts and controls require Kani; reviewed-cut substitution, canonical/unit domains, frame/loop induction and cohort association remain Lean-only.'
   if deps:why+=' OPEN conservative children: '+', '.join(deps)+'.'
   rem+=f"| {rid} | {r['function'].split('::',1)[1]} | {why} | {live(r)} |\n"
 rem+='\n## Outside the599function count\n\n(aw) NJW-aw-TX2:115-off-domain CLOSED: generalized SAME-current-word full Result/prefix law admitted; no parent promotion. NJY-B1 Box/ProgramError wrapper48/49 and actual production Pool joins remain OPEN. Each named Pool status is re-listed in NKH_PHYSICAL.md. K086 and(aj)(a) remain unresolved. L187cold release/L188artifact/extraction gates remain separate.\n'
 (E/'NKH_REMAINING.md').write_text(rem)

if __name__=='__main__':
 import lzma
 ledger=json.loads(lzma.decompress((E/'NKH_LEDGER.json.xz').read_bytes()))
 report(ledger,json.loads((E/'NKH_RESOURCES.json').read_text()))
