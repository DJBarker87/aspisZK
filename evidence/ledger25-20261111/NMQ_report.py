"""Recompute physical distances from the retained canonical graph."""
from pathlib import Path
import json,collections,heapq
E=Path(__file__).resolve().parent
LIVE={**{r:'NMP_ tx1-observed3'for r in ['TX1:137','TX1:087']},'TX1:136':'NMO_ tx1-finish4',**{r:'NMM_ tx2-adapters5;217/234 then233'for r in ['TX2:217','TX2:234','TX2:233']},**{r:'UNOWNED'for r in ['TX1:094','TX1:328','TX1:345','TX1:344','TX1:333','TX1:330','TX2:242','TX2:241','TX2:240','TX2:221','TX2:213']}}
def report(ledger,resources):
 rows=ledger['rows'];parts={k:[r for r in rows if r['function'].startswith(p)]for k,p in [('b','programs/'),('c','crates/')]};counts={k:dict(collections.Counter(r['status']for r in rs))for k,rs in parts.items()};assert[len(parts[k])for k in ['b','c']]==[53,546]
 out='# NLX physical association distances\n\nTarget not yet established. Eighteenth all-slices composition test. Counts are conditional native/source association obligations under NDT semantics, not runtime measurements or security bits. All599 rows and canonical edges are retained.\n\n| Part | Total | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
 for k,rs in parts.items():out+=f"| (ao)(3)({k}) | {len(rs)} | {counts[k].get('CLOSED',0)} | {counts[k].get('OPEN',0)} | {counts[k].get('QUALIFIED',0)} |\n"
 out+='\n## Shortest OPEN spine paths\n\nBFS minimizes canonical call edges at the same ledger24 targets. Independent Dijkstra minimizes (OPEN rows, call edges), including entry row cost. CLOSED children do not close their parent; conservative069→202 is retained.\n';spines=[];allpaths={}
 for tx,entry,finish in [('TX1','330','094'),('TX2','213','115')]:
  rs=[r for r in rows if r['transaction']==tx];bf={r['function']:r for r in rs};br={r['row']:r for r in rs};start=br[tx+':'+entry]['function'];target=br[tx+':'+finish]['function'];q=collections.deque([[start]]);seen={}
  while q:
   p=q.popleft();f=p[-1]
   if f in seen:continue
   seen[f]=p
   for child in bf[f]['canonical_callees']:
    if child in bf and child not in p:q.append(p+[child])
  p=seen[target];opens=sum(bf[z]['status']=='OPEN'for z in p);heap=[(int(bf[start]['status']=='OPEN'),0,[start])];costs={};best=None
  while heap:
   oc,edges,path=heapq.heappop(heap);tail=path[-1]
   if tail in costs:continue
   costs[tail]=(oc,edges)
   if tail==target:best=dict(open_distance=oc,edges=edges,path=[bf[z]['row']for z in path]);break
   for ch in bf[tail]['canonical_callees']:
    if ch in bf and ch not in path:heapq.heappush(heap,(oc+int(bf[ch]['status']=='OPEN'),edges+1,path+[ch]))
  packet=[dict(row=bf[z]['row'],function=z,status=bf[z]['status'])for z in p];spines.append(dict(transaction=tx,path=packet,open_distance=opens,edges=len(p)-1,minimum_open=best));assert (best['open_distance'],best['edges'])==(opens,len(p)-1)
  out+='\n'+tx+': '+' → '.join(x['row']+' '+x['function'].split('::')[-1]+' ['+x['status']+']'for x in packet)+f'. OPEN distance {opens}; {len(p)-1} call edges. Independent minimum-OPEN search agrees.\n'
  allpaths[tx]=[dict(row=bf[f]['row'],path=[bf[z]['row']for z in path],call_edges=len(path)-1,open_distance=sum(bf[z]['status']=='OPEN'for z in path))for f,path in seen.items()if bf[f]['status']=='OPEN']
 out+='\n## OPEN rows by source file and owning live job\n';grouped=collections.defaultdict(list)
 for r in rows:
  if r['status']=='OPEN':grouped[r['function'].split('::')[0]].append(r)
 for file,rs in sorted(grouped.items()):
  out+='\n### '+file+'\n\n| Row | Function | Owner |\n|---|---|---|\n'
  for r in rs:out+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {LIVE[r['row']]} |\n"
 unowned=[r['row']for r in rows if r['status']=='OPEN'and LIVE[r['row']].startswith('UNOWNED')]
 out+='\nUnowned OPEN: '+', '.join(unowned)+'. Dependency order (child before parent): TX1 094 > 328 > 345 > 344 > 333 > 330; TX2 242 > 241 > 240 > 221 > 213. Live rows are attempted independently along real call dependencies; no unowned entry row is held behind an unrelated row. No sibling worktree was edited.\n'
 out+='\n## Argument-domain boundary\n\nTX2:064 uses exclusively NMN_064.root, composed with canonical parse_shape, mark and NLT_CompleteRoot.root at SAME arguments. NLT_Root.root is withdrawn from credit. The four own-input clauses proof57607, checkpoint1768, public<=1880 and NLP_InputDomain.Root0 checkpoint proof are explicit bf2 predicates on ORIGINAL inputs, recorded at OPEN TX2:241 in NMQ_PARENT_CLAUSES.json. NMF_GameRoot.root0_or_existing_collision discharges literal Root0 at the SAME accepted headline occurrence outside the headline EXISTING charged BinRawByteCollisionTargets.event. NMN_Headline.accepted_occurrence installs064 there; no global Root0/hash-injectivity premise or new trust. RuntimePersistence alone is insufficient; NMF also proves saved-writer/reached-resume proof-digest binding. Every actual241 getter/encoder/domain/native association remains OPEN. Independent stopped common carries only event prefix; no post-abort world.\n'
 out+='\n## (ao)(3)(d) Pool named obligations: read-only Stream C context\n\nSource: evidence/pool-ledger1-20261110/PCE_LEDGER.json.xz, PCE_COMPOSITION.md and PCE_HANDOFF.md. No Pool promotion in this job. Pool397 ON =278 new +119 shared bodies;15/278 new helpers CLOSED,263 OPEN; all119 shared bodies retain Stream A ownership. Three ON guard owners OPEN; three OFF owners remain outside ON counts. Three held sites (two ON/one OFF) remain OPEN. Exact frozen Pool b936275465600469312d1f058cdc91ea2a11f3dc; ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc; historical121f3e29 superseded. No verifier row depends on Pool ELF.\n\n'
 out+='| Held site | Scope | Status |\n|---|---|---|\n| POOL:328 process_pair_forest_deposit_with_runtime_v1 | ON | OPEN: exact guarded transfer/CPI continuation |\n| POOL:330 process_pair_forest_terminal_with_verifier_v1 | ON | OPEN: guarded terminal/marker and verifier/token continuation |\n| POOL:400 process_pair_withdrawal_with_verifier_v1 | OFF review | OPEN; excluded from ON counts |\n\n'
 pool=(E.parent/'pool-ledger1-20261110/PCE_COMPOSITION.md').read_text();out+=pool[pool.index('## NIB-P1'):]
 out+='\n## Status and trust inventory\n\nK086: NHP_K086 core::cell::panic_already_mutably_borrowed::do_panic::runtime, core/cell.rs:898; unsupported runtime-formatted panic,1/1024failed,12unreachable. Liveness/abort; production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING: same-game Pool settlement optionA versus conditional external Pool association optionB.\n\nRuntimeCpiAccountView ADDED-LEAD-20261110 is carried under(c-a), soundness-side only: on a returning Pool CPI, keys absent from metas retain data/length/lamports/owner; passed keys in metas reflect callee final values. Exact metas/infos, cell separation and SDK counters/handles remain obligations. It gives no CPI success, token/system semantics, rollback, rent or readonly entry. RuntimeCpiReadonlyEntry7 PENDING/UNUSED. Extraction trust narrowing(bc) is a RECLASSIFICATION, not removal: post-loop explicit return/? exits need pattern exclusion or native exit certification. All prior trust retained; no cryptographic row changed. RuntimePersistence is data-only; initial Pool admission seven fields only; digest/error43/44, quantified PDA38; L154 statement parameter, frozen3, narrowedD188 and100-bit PER-ATTEMPT/privacy/two-transaction contract unchanged.\n'
 (E/'NMQ_PHYSICAL.md').write_text(out)
 (E/'NMQ_PHYSICAL.json').write_text(json.dumps(dict(entry_native_counts=counts,shortest_spines=spines,all_open_shortest_paths=allpaths,open_by_source={f:[dict(row=r['row'],function=r['function'],live_owner=LIVE[r['row']])for r in rs]for f,rs in grouped.items()},unowned_open_rows=unowned,pool_context='read-only PCE; no promotion'),indent=1)+'\n')
 rem='# NLX remaining obligations\n\nTarget not yet established. '+str(resources['scopes'])+'/40 Lean/link/audit scopes;0Kani/0extraction. No further ledger-only replay closes these rows. Existing Lean-only folds belong to the named live jobs; new native segments/controls require their Kani authority under(bj)/(bl), which this job does not have.\n'
 for file,rs in sorted(grouped.items()):
  rem+='\n## '+file+'\n\n| Row | Member | Remaining obligation | Owner |\n|---|---|---|---|\n'
  for r in rs:
   if r['row']=='TX2:064':why='Not applicable:064 is CLOSED only after the full gate.'
   elif r['row'].startswith('TX1:')and r['row']in ['TX1:094','TX1:087','TX1:137','TX1:136']:why='Full driver fold over ONE actual native invocation, SAME original inputs/child calls, every Result/error/abort, owned state/cleanup/frame and ordered effects; internally substitute CLOSED child packets and prove their caller domains. Lean folds continue in owner job; missing native segments/controls need that job Kani budget.'
   else:why='Complete frozen entry/adapter transcription under(bj)/(bl), whole actual-parent native cuts with matched controls, NLF SDK law and CLOSED children at SAME original account descriptors, buffers, borrow tokens, allocator events/PDA reply. Full Result/error/abort and ordered effects; source support alone does not close it.'
   deps=[z['row']for z in rows if z['transaction']==r['transaction']and z['status']=='OPEN'and z['function']in r['canonical_callees']]
   if deps:why+=' OPEN direct children: '+', '.join(deps)+'.'
   rem+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {why} | {LIVE[r['row']]} |\n"
 rem+='\nPool.prefix_to_cpi, NIB-P1/P2/P3/P4 and POOL.read_to_settlement retain their PCE statuses; exact member/status tables are in NMQ_PHYSICAL.md. All3 ON guard owners and3 OFF review owners remain OPEN. Latest available Pool ledger PCE15 CLOSED helpers are read-only context, no Pool promotion. Later Stream C packet claims are not silently inserted into that ledger. K086 reachability/exclusion, owner(aj)(a), L187 cold release replay/L188 artifact/extraction association and NKT-F2/F3 provenance remain; NMQ_PROVENANCE.json records the current conservative affected CLOSED rows. No remaining job-owned mathematical theorem is hidden behind Kani exhaustion; this refresh has no owned native function work and does not duplicate live owner work.\n'
 (E/'NMQ_REMAINING.md').write_text(rem)
 return counts,spines,unowned
