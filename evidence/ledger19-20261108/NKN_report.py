from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;P=E.parent/'ledger18-20261108'
def live(r):
 rid=r['row']
 if rid=='TX2:065':return 'NKE_ tx2-native9 (M01 join)'
 if rid=='TX2:124':return 'NKK_ tx2-resume'
 if rid in ['TX1:081','TX1:082','TX1:083','TX1:084','TX2:053','TX2:054','TX2:055']:return 'NKL_ batch-merkle3'
 if rid in ['TX1:NGB002','TX1:NGB004','TX1:NGB006']:return 'NKM_ circle-points'
 if rid=='TX1:136'or(rid.startswith('TX1:')and('pair_forest_copy_terminal.rs' in r['function']or'pair_forest_semantic_terminal.rs'in r['function'])):return 'NKI_ terminal4 (256 and terminal parents, including225)'
 return 'UNOWNED in current brief; lead routing required'
def report(ledger,resources):
 rows=ledger['rows'];parts={k:[r for r in rows if r['function'].startswith(p)]for k,p in [('b','programs/'),('c','crates/')]};assert [len(parts[k])for k in ['b','c']]==[53,546]
 counts={k:dict(collections.Counter(r['status']for r in rs))for k,rs in parts.items()};paths=[]
 out='# NKN physical association distances\n\nTarget not yet established. Twelfth all-slices gate admits exactly11 new occurrences. Distances are remaining conditional native/source associations, not elapsed runtime or a headline proof.\n\n| Part | Total | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
 for g,rs in parts.items():
  c=counts[g];out+=f"| (ao)(3)({g}) | {len(rs)} | {c.get('CLOSED',0)} | {c.get('OPEN',0)} | {c.get('QUALIFIED',0)} |\n"
 out+='\nEntry38/53 CLOSED (15 remain); native forest515/546 CLOSED (31 remain). Total553 CLOSED/0 QUALIFIED/46 OPEN. No helper promotion closes an unsubmitted parent.\n\n## Shortest OPEN spines\n\nBFS over every retained canonical edge, including069→202 marked spurious-by-name.\n'
 for tx,start,target in [('TX1','330','094'),('TX2','213','115')]:
  rs=[r for r in rows if r['transaction']==tx];bf={r['function']:r for r in rs};br={r['row']:r for r in rs};q=collections.deque([[br[tx+':'+start]['function']]]);seen=set();found=None
  while q:
   p=q.popleft();tail=p[-1]
   if tail==br[tx+':'+target]['function']:found=p;break
   if tail in seen:continue
   seen.add(tail)
   for c in bf[tail]['canonical_callees']:
    if c in bf and c not in p:q.append(p+[c])
  assert found
  packet=[dict(row=bf[f]['row'],function=f,status=bf[f]['status'],owner=bf[f]['owner_module'])for f in found];ps=dict(transaction=tx,edges=len(found)-1,path=packet,remaining_open=[r['row']for r in packet if r['status']=='OPEN']);paths.append(ps)
  out+='\n'+tx+': '+' → '.join(r['row']+' '+r['function'].split('::')[-1]+' ['+r['status']+']'for r in packet)+f".\n\nOPEN distance {len(ps['remaining_open'])}; {ps['edges']} call edges.\n"
 grouped=collections.defaultdict(list)
 for r in rows:
  if r['status']=='OPEN':grouped[r['function'].split('::')[0]].append(r)
 out+='\n## OPEN rows by source and owning live job\n'
 for f,rs in sorted(grouped.items()):
  out+='\n### '+f+'\n\n| Row | Function | Owning live job |\n|---|---|---|\n'
  for r in rs:out+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {live(r)} |\n"
 unowned=[r['row']for r in rows if r['status']=='OPEN'and live(r).startswith('UNOWNED')]
 out+='\n## Explicit unowned OPEN rows\n\n'+', '.join(unowned)+'.\n'
 pool=(P/'NKH_PHYSICAL.md').read_text().split('## (ao)(3)(d): named Pool obligations',1)[1].split('\nNKH makes no production Pool promotion',1)[0]
 out+='\n## (ao)(3)(d): named Pool obligations'+pool
 out+='\nNKN grants no production Pool credit. All named Pool obligations retain their status. RuntimePersistence data-only, initial Pool entry seven fields, RuntimeCpiReadonlyEntry7 unused; op38 quantified, digest/error op43/op44. K086 remains a liveness/abort finding with production reachability/exclusion UNPROVED. Owner decision(aj)(a) PENDING.\n'
 (E/'NKN_PHYSICAL.md').write_text(out)
 (E/'NKN_PHYSICAL.json').write_text(json.dumps(dict(entry_native_counts=counts,shortest_spines=paths,open_by_source={k:[dict(row=r['row'],function=r['function'],live_owner=live(r))for r in rs]for k,rs in grouped.items()},unowned_open_rows=unowned,supplemental_child_obligations=ledger['supplemental_child_obligations'],Pool_basis='NKH_PHYSICAL.md; full named statuses retained verbatim'),indent=1)+'\n')
 rem='# NKN remaining obligations\n\nTarget not yet established.40/40 Lean/link/audit scopes;0Kani/0extraction. Eleven candidates admitted only after the full gate;46 occurrences remain OPEN. The original obligations and parent clauses remain in NKN_LEDGER.json.xz. This refresh has no Kani/extraction authority. Existing reviewed-cut substitution, domain/frame/induction/trace joins remain Lean-only work for the owning lanes; native gaps below require matched cuts/controls in those lanes, not an audit rerun.\n'
 for f,rs in sorted(grouped.items()):
  rem+='\n## '+f+'\n\n| Row | Member | Remaining obligation | Live owner |\n|---|---|---|---|\n'
  for r in rs:
   deps=[v['row']for v in rows if v['transaction']==r['transaction']and v['status']=='OPEN'and v['function']in r['canonical_callees']]
   rid=r['row']
   if rid in ['TX1:083','TX2:055']:why='NKB-F1: exact returned Err(Parse)/Err(Merkle) versus reused pending-none/fail. Need explicit frozen Result segment cuts/control plus same ordered-prefix rejection transport to adopted model (bb)(1)-(2). Native new cuts require Kani; transport/frame/propagation is Lean-only. TX2 uses <=12 indices/9216-byte entry, superseded10-leaf clause retained.'
   elif rid in ['TX1:081','TX1:082','TX2:053','TX2:054']:why='Propagate exact batch_tree returned errors at SAME ? sites, ordered prefix and no suffix; child tree OPEN. Native source segment/call-site controls where absent require Kani; child-domain/Result/effect composition is Lean-only.'
   elif rid=='TX1:084':why='Compose SAME canonical scan over CLOSED189 echeck, exact parser/loop frame and error prefixes. Missing native parent cut/control needs Kani; child instantiation and finite induction are Lean-only.'
   elif rid=='TX2:065':why='M01 SAME resume/query/flush/finish parent invocation/log assembly. Generalized current-word115 supplement remains CLOSED outside599; batch M02 remains OPEN. Missing native parent cuts/control need Kani; child/domain/source-prefix composition is Lean-only.'
   elif rid=='TX2:124':why='Complete resume native log/cursor/owned-carrier/cleanup assembly at SAME original bytes and all errors. Missing native windows/control need Kani; CLOSED Reader/header/parser/domain/effect substitutions and allocator assembly are Lean-only.'
   elif rid in ['TX1:NGB002','TX1:NGB004','TX1:NGB006']:why='Complete circle-point source/native/cohort association including canonical parameter and branch domains. Missing native scalar/call windows and matched controls need Kani; field rule-A substitution/case split and domain transport are Lean-only.'
   elif live(r).startswith('NKI'):why='SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only.'
   elif f.startswith('programs/'):why='Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry.'
   else:why='Complete SAME-function native/source/full Result/abort/post/frame/ordered-effects packet remains unadmitted. Missing native one-step/call-site cuts/control need Kani; existing-cut substitution/canonical unit domains/frame/induction/cohort joins are Lean-only.'
   if deps:why+=' OPEN children: '+', '.join(deps)+'.'
   rem+=f"| {rid} | {r['function'].split('::',1)[1]} | {why} | {live(r)} |\n"
 rem+='\n## Separate obligations\n\nAll named Pool obligations in NKN_PHYSICAL.md remain OPEN/conditional as named; no finite complete production inventory is claimed. NJY-B1 Box/ProgramError wrappers48/49 remain OPEN. Entry/op9/native parent/Pool continuation, L187 cold replay and L188 artifact/extraction joins remain. K086 and owner(aj)(a) remain unresolved. Retained off-domain115 supplement is CLOSED; no new parent credit.\n'
 (E/'NKN_REMAINING.md').write_text(rem)
 return counts,paths,unowned
