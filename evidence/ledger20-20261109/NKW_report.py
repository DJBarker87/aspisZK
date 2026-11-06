from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent
def live(r):
 rid=r['row']
 if rid=='TX2:065':return 'NKO_ tx2-native10 C02-C09'
 if rid in ['TX1:136','TX1:137','TX1:087','TX1:094']:return 'NKQ_ tx1-driver'
 if rid in ['TX1:'+s for s in ['232','251','250','261','225','220','218','237','263','256']]:return 'NKR_ terminal5'
 if rid=='TX2:124':return 'NKU_ tx2-resume2'
 if rid in ['TX2:053','TX2:054','TX2:055','TX1:081','TX1:082','TX1:083']:return 'NKV_ batch-merkle4'
 return 'UNOWNED; lead routing required'
def report(ledger,resources):
 rows=ledger['rows'];counts=ledger['counts'];parts={k:[r for r in rows if r['function'].startswith(p)]for k,p in [('b','programs/'),('c','crates/')]};cs={k:dict(collections.Counter(r['status']for r in rs))for k,rs in parts.items()};assert [len(parts[k])for k in ['b','c']]==[53,546]
 out='# NKW physical association distances\n\nTarget not yet established. Thirteenth all-slices composition test. Distances count remaining conditional native/source associations, not runtime or headline proof.\n\n| Part | Total | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
 for g,rs in parts.items():out+=f"| (ao)(3)({g}) | {len(rs)} | {cs[g].get('CLOSED',0)} | {cs[g].get('OPEN',0)} | {cs[g].get('QUALIFIED',0)} |\n"
 out+='\n## Shortest OPEN spines\n\nBFS retains every canonical edge, including the spurious-by-name069→202 edge. No unsubmitted parent is promoted.\n';paths=[]
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
  packet=[dict(row=bf[f]['row'],function=f,status=bf[f]['status'])for f in found];x=dict(transaction=tx,edges=len(found)-1,path=packet,remaining_open=[r['row']for r in packet if r['status']=='OPEN']);paths.append(x)
  out+='\n'+tx+': '+' → '.join(r['row']+' '+r['function'].split('::')[-1]+' ['+r['status']+']'for r in packet)+f". OPEN distance {len(x['remaining_open'])}; {x['edges']} call edges.\n"
 grouped=collections.defaultdict(list)
 for r in rows:
  if r['status']=='OPEN':grouped[r['function'].split('::')[0]].append(r)
 out+='\n## OPEN rows by source file and live job\n'
 for file,rs in sorted(grouped.items()):
  out+='\n### '+file+'\n\n| Row | Function | Live owner |\n|---|---|---|\n'
  for r in rs:out+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {live(r)} |\n"
 unowned=[r['row']for r in rows if r['status']=='OPEN'and live(r).startswith('UNOWNED')];out+='\n## Unowned OPEN rows\n\n'+', '.join(unowned)+'.\n'
 pool=(E.parent/'ledger19-20261108/NKN_PHYSICAL.md').read_text().split('## (ao)(3)(d): named Pool obligations',1)[1].split('\nNKN grants no production Pool credit.',1)[0]
 out+='\n## (ao)(3)(d): named Pool obligations'+pool
 out+='\nNKS inventory only:613 ON source occurrences,119 body matches cover183 of599 verifier occurrences,494 outside that basis; four OFF-only owners retained separately. No Pool rows added to599 and no Pool status transfer. All production joins remain OPEN. RuntimeCpiReadonlyEntry7 PENDING/UNUSED. Owner(aj)(a) PENDING (same-game settlement A versus external Pool-association conditional B). K086 liveness/abort; production reachability/exclusion UNPROVED. Initial Pool seven-field entry trust supplies no CPI continuation frame. RuntimePersistence data-only; op38 quantified; digest/error43/44.\n'
 (E/'NKW_PHYSICAL.md').write_text(out);(E/'NKW_PHYSICAL.json').write_text(json.dumps(dict(entry_native_counts=cs,shortest_spines=paths,open_by_source={k:[dict(row=r['row'],function=r['function'],live_owner=live(r))for r in rs]for k,rs in grouped.items()},unowned_open_rows=unowned,Pool_inventory_only=dict(ON=613,outside599=494,matched_occurrences=183,body_matches=119),supplemental_child_obligations=ledger.get('supplemental_child_obligations',[])),indent=1)+'\n')
 rem='# NKW remaining obligations\n\nTarget not yet established. All40 authorized Lean/link/audit scopes consumed;0Kani/0extraction. No native/extraction budget exists in this job. Each remaining member below requires a complete native/source/Result/effects association. Audit repetition cannot fill it. Existing-cut substitutions, domain and induction work can continue in the owning lanes; new native cuts/controls require their Kani authority.\n'
 rejected={x['row']:x['missing_clause']for x in json.loads((E/'NKW_CANDIDATE_REVIEW.json').read_text())['rows']if x['missing_clause']}
 for file,rs in sorted(grouped.items()):
  rem+='\n## '+file+'\n\n| Row | Member | Exact remaining work | Owner |\n|---|---|---|---|\n'
  for r in rs:
   rid=r['row'];deps=[v['row']for v in rows if v['transaction']==r['transaction']and v['status']=='OPEN'and v['function']in r['canonical_callees']]
   if rid in rejected:why=rejected[rid]+' Lean-only value/domain facts remain usable; complete native allocation/loop-body association needs new cuts if not derivable from existing ones.'
   elif rid in ['TX1:083','TX2:055']:why='NKB-F1/NKT-F1: exact returned Parse/Merkle errors lost in post-loop emission. Need explicit-Result frozen native segment/control and same first-rejection prefix transport under(bb)/(bc); never reuse pending-none as Result equality.'
   elif rid in ['TX1:081','TX1:082','TX2:053','TX2:054']:why='Propagate exact complete batch_tree Result/errors at SAME ? sites and ordered prefix, no rejected suffix. TX2≤12indices/9216byte entry; TX1≤10; original superseded clause retained. Child tree remains OPEN.'
   elif rid=='TX2:065':why='NKO C02-C09 native SAME resume/query/flush/finish call chain, all Results/abort/post/frames; source/native one-step/log association and domain composition. Generalized current-word115 supplement retained; no history/NoBad replacement.'
   elif rid=='TX2:124':why='SAME original resume bytes/cursor/owned allocation/read/cleanup chain and every error; compose CLOSED Readers and decoder domains with native parent cuts.'
   elif live(r).startswith('NKQ'):why='Complete actual driver native invocation, SAME parent/child calls and original accounts/proof, all Result/error/abort/frames and ordered effects; substitute CLOSED child domains internally; entry continuation remains unproved.'
   elif live(r).startswith('NKR'):why='Complete terminal native/source/cohort packet at SAME selectors/opening arrays/canonical budget; use CLOSED NKJ040/041/043 at225 and NKG308 at237. Native parent cuts/controls and exact Result/loop/frame association still missing.'
   elif file.startswith('programs/'):why='Actual entry/adapter SAME input/account/SDK/borrow/drop/PDA/allocator/current slot association; full Result/errors and ordered effects. Existing child support does not supply production entry/continuation law.'
   else:why='Complete same-function native/source/cohort Result, abort/post/frame and chronological effects packet remains unadmitted; matched native one-step/call-site cuts absent or uncomposed. Domain/frame/induction are Lean-only; absent native cuts need owning lane Kani.'
   if deps:why+=' OPEN children: '+', '.join(deps)+'.'
   rem+=f"| {rid} | {r['function'].split('::',1)[1]} | {why} | {live(r)} |\n"
 rem+='\nSeparate OPEN obligations: all named Pool producers/continuations above, K086, owner(aj)(a), entry/op9/native forest, L187cold release replay, L188artifact/extraction. NKT-F2 exact tool origin for274emission blobs; NKT-F3 root provenance for two inherited to_limbs packets (no new credit). No cryptographic/runtime trust row is removed or added. NKW composition is focused, not a cold release rebuild.\n'
 (E/'NKW_REMAINING.md').write_text(rem)
 return cs,paths,unowned
