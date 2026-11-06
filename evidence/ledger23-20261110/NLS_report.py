from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent
TERMINAL={'TX1:'+s for s in ['261','237','263','256']};DRIVER={'TX1:136'};PREPARE={'TX1:'+s for s in ['137','087','094']};ENTRY={'TX2:'+s for s in ['064','241','240','221','213']};ADAPTER={'TX2:'+s for s in ['217','234','233','242']};BATCH=set()
def live(r):
 rid=r['row']
 if rid in TERMINAL:return 'NLH_ terminal6'
 if rid in DRIVER:return 'NLI_ tx1-finish'
 if rid in {'TX1:137','TX1:087'}:return 'NLR_ tx1-observed'
 if rid in {'TX1:328','TX1:345','TX1:344','TX1:333','TX1:330'}:return 'NLQ_ tx1-entry2'
 if rid in ENTRY:return 'NLM_ tx2-entry2'
 if rid in ADAPTER:return 'UNOWNED; paused by lead'
 return 'NLP_ tx2-common' if rid=='TX2:065' else 'UNOWNED; lead routing required'
def report(ledger,resources):
 rows=ledger['rows'];parts={k:[r for r in rows if r['function'].startswith(p)]for k,p in [('b','programs/'),('c','crates/')]};cs={k:dict(collections.Counter(r['status']for r in rs))for k,rs in parts.items()};assert [len(parts[k])for k in ['b','c']]==[53,546]
 out='# NLO physical association distances\n\nTarget not yet established. Sixteenth all-slices composition test. Distances count remaining conditional native/source associations under NDT semantics; they are not runtime measurements or headline soundness. No edge is pruned.\n\n| Part | Total | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
 for g,rs in parts.items():out+=f"| (ao)(3)({g}) | {len(rs)} | {cs[g].get('CLOSED',0)} | {cs[g].get('OPEN',0)} | {cs[g].get('QUALIFIED',0)} |\n"
 out+='\n## Shortest OPEN spines\n\nSame targets as NLO ledger22: TX1 entry330→driver094, TX2 entry213→finish115. BFS minimizes canonical call edges and counts OPEN rows along the selected spine; CLOSED child rows do not promote an unsubmitted parent. Conservative069→202 remains.\n';paths=[];distances={}
 for tx,start,target in [('TX1','330','094'),('TX2','213','115')]:
  rs=[r for r in rows if r['transaction']==tx];bf={r['function']:r for r in rs};br={r['row']:r for r in rs};q=collections.deque([[br[tx+':'+start]['function']]]);found={}
  while q:
   p=q.popleft();tail=p[-1]
   if tail in found:continue
   found[tail]=p
   for c in bf[tail]['canonical_callees']:
    if c in bf and c not in p:q.append(p+[c])
  f=found[br[tx+':'+target]['function']];packet=[dict(row=bf[v]['row'],function=v,status=bf[v]['status'])for v in f];x=dict(transaction=tx,edges=len(f)-1,path=packet,remaining_open=[r['row']for r in packet if r['status']=='OPEN']);paths.append(x)
  out+='\n'+tx+': '+' → '.join(r['row']+' '+r['function'].split('::')[-1]+' ['+r['status']+']'for r in packet)+f". OPEN distance {len(x['remaining_open'])}; {x['edges']} call edges.\n"
  distances[tx]=[dict(row=bf[v]['row'],shortest_call_edges=len(p)-1,open_count=sum(bf[z]['status']=='OPEN'for z in p),path=[bf[z]['row']for z in p])for v,p in found.items()if bf[v]['status']=='OPEN']
 grouped=collections.defaultdict(list)
 for r in rows:
  if r['status']=='OPEN':grouped[r['function'].split('::')[0]].append(r)
 out+='\nIndependent minimum-OPEN weighted graph search agrees with both selected spines (NLS_SPINE_PREFLIGHT.json): TX1 distance6/5edges; TX2 distance6/6edges. All canonical edges retained.\n'
 out+='\n## OPEN rows by source file and live job\n'
 for file,rs in sorted(grouped.items()):
  out+='\n### '+file+'\n\n| Row | Function | Live owner |\n|---|---|---|\n'
  for r in rs:out+=f"| {r['row']} | {r['function'].split('::',1)[1]} | {live(r)} |\n"
 unowned=[r['row']for r in rows if r['status']=='OPEN'and live(r).startswith('UNOWNED')];out+='\n## Unowned OPEN rows\n\n'+', '.join(unowned)+'. NKV_, NLL_, NLJ_ RowSpec_094 and NLK_ are supporting evidence only. TX1:094 is unowned; TX2:217/234/233/242 are paused by the lead. NLF_ sdk-borrow supplies shared support for entry rows and Pool guard owners; it closes no row here.\n'
 out+='\n## Native input clauses\n\nTX2:124 closes only within proof57607/public0..1880 native scope. TX2:065 and upward064/241/240/221/213 retain that OPEN obligation at SAME resume arguments, including source serialized-public provenance. The broader Lean source equation does not widen native credit. CLOSED TX1:251 discharges235 canonical frontier/opening/high at actual arguments. NLH261 discharges232/233/250/228/229 at its actual canonical carriers; NLH237 discharges261/218 and deterministic308 at its actual gathered arrays, and derives amount canonicality from its own precheck; NLH263/256 preserve full Results at SAME arguments. All predecessor clauses remain recorded with their new dispositions; own Public/claims/point/challenge clauses remain on OPEN caller136. (bf) own-argument clauses are recorded verbatim on TX2:065 C04, TX1:094/087 and every internal child occurrence. NLE_ source-level extent/public/range discharge is SUPPORT ONLY on065/064; native caller association is still required. TX1:237 consumes CLOSED deterministic TX1:308, never an oracle.\n'
 out+='\n## (ao)(3)(d): named Pool obligations\n\nPool revision b936275465600469312d1f058cdc91ea2a11f3dc, ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc; historical121f3e29… is superseded for Pool only. No verifier row depends on Pool ELF. The599 verifier basis is unchanged; zero production Pool-consumer occurrences are credited. Three inherited CLOSED helper entries (pair_forest_dispatch.supported_loader, processor.require_transaction_level_invocation_v1, error.convertPoolError) are not whole-Pool closure.\n\nNKZ inventory only:397 ON occurrences,278 new to basis,119 shared bodies matching183/599, D30. Six retained exclusive owners(3 ON/3 OFF), three held sites(2 ON/1 OFF), all OPEN;15 accessors, seven data_is_empty sites. No native closure follows from body matching or legacy deletion.\n'
 # Import the named current obligations verbatim, retaining the original source names and OFF dispositions.
 pool=(E/'NLO_POOL_INPUT.md').read_text();out+='\n'+pool.split('\n',1)[1]
 out+='\n### Legacy owner disposition\n\nSeven former guard owners and transition::apply_authorized_append_after_checked_state_v1 held callback were REMOVED SOURCE, not proved: close_program_account_v1, process_prepare_settlement_with_runtime_v1, process_settle_prepared_with_runtime_v1, create_and_write_marker_v1, process_withdrawal_with_runtime_v1, initialize_pool_accounts_v1, apply_authorized_append_after_checked_state_v1. Exact old/new rows and all surviving ON/OFF sites: NKZ_DIFF.md. Original13→6guard owners,4→3held sites,21→15accessors.\n'
 out+='\nOwner(aj)(a) PENDING: same-game settlement optionA versus external Pool-association conditionalB. K086 is liveness/abort; production reachability/exclusion UNPROVED. RuntimeCpiReadonlyEntry7 PENDING/UNUSED. Initial Pool admission seven fields only; no CPI continuation/frame. RuntimePersistence data-only; PDA op38 quantified; digest/error43/44. L154 statement parameter; extraction/P6/D188 option-A retained. No runtime or cryptographic trust changes.\n'
 (E/'NLO_PHYSICAL.md').write_text(out);(E/'NLO_PHYSICAL.json').write_text(json.dumps(dict(entry_native_counts=cs,shortest_spines=paths,minimum_open_spine_check=json.loads((E/'NLS_SPINE_PREFLIGHT.json').read_text()),all_open_shortest_paths=distances,open_by_source={k:[dict(row=r['row'],function=r['function'],live_owner=live(r))for r in rs]for k,rs in grouped.items()},unowned_open_rows=unowned,Pool_inventory_only=dict(ON=397,new_to_basis=278,D=30,guard_owners=6,held_sites=3,production_closed_credit=0)),indent=1)+'\n')
 rem='# NLO remaining obligations\n\nTarget not yet established. '+str(resources['scopes'])+'/40 serial Lean/link/audit scopes consumed;0Kani/0extraction. All four submitted candidates pass only through the recorded gate. No source/ELF/runtime/cryptographic claim is enlarged. Every remaining row needs the named complete native/source/Result/effects packet; audit repetition cannot fill it. Existing cuts, domain and induction can continue in owner jobs; absent native cuts and controls require those jobs\' Kani authority.\n'
 for file,rs in sorted(grouped.items()):
  rem+='\n## '+file+'\n\n| Row | Member | Exact remaining work | Owner |\n|---|---|---|---|\n'
  for r in rs:
   rid=r['row'];deps=[v['row']for v in rows if v['transaction']==r['transaction']and v['status']=='OPEN'and v['function']in r['canonical_callees']]
   if rid in ['TX1:083','TX2:055']:why='NKB-F1/NKT-F1: preserve exact returned Parse/Merkle error lost in post-loop emission; actual native Result segment/control and first-rejection prefix transport under(bb)/(bc). No pending-none surrogate.'
   elif rid in BATCH:why='Exact complete child batch Result/errors at SAME ? sites and ordered prefix; TX1<=10/TX2<=12indices/9216-byte scope. No rejected suffix. Native parent cuts need child tree law.'
   elif rid=='TX2:065':why='NLB conditional fold is support only: instantiate full child parent packets at SAME original arguments; batch child053 is CLOSED on its recorded own-input domain. Consume NKU124 with proof57607/public<=1880 derived from admitted serialized-public caller context. C02-C09 full native chain, abort/post/frame/log association still unadmitted. Generalized current-word115 supplement retained, no NoBad/history premise.'
   elif rid in DRIVER or rid in PREPARE:why='Actual driver fold over SAME native invocation, original accounts/proof and child arguments. Every Result/error/abort/post/cleanup/frame and chronological effects required. CLOSED child packets substituted internally; no independent endpoint/accepted-parent hypothesis.'
   elif rid in TERMINAL:why='NLH complete terminal parent native/source/cohort fold at SAME canonical arrays/selectors/budget; internal CLOSED235/234/233/260 and225 children at actual arguments. Full loop/Result/error/abort/frame association; no new native cuts in this refresh.'
   else:why='Actual entry/adapter SAME account/input/SDK guard identity and counter lifetime, PDA/allocator/current-slot association; full native Result/errors/abort and ordered effects. NLF shared borrow law is support only; parent continuation remains unproved.'
   if deps:why+=' OPEN children: '+', '.join(deps)+'.'
   rem+=f"| {rid} | {r['function'].split('::',1)[1]} | {why} | {live(r)} |\n"
 rem+='\nAll named Pool producers NIB-P1..P4, POOL.prefix_to_cpi and POOL.read_to_settlement production association remain OPEN; the read-to-settlement MODEL theorem is conditional. All6surviving guard owners/3held sites OPEN with ON/OFF scopes in NLO_PHYSICAL.md. K086/owner(aj)(a), entry/op9/native forest, L187cold replay/L188artifact/extraction remain. NKT-F2 tool origin274emissions and F3two inherited zero-root to_limbs packet provenance OPEN. No remaining row can be closed merely by an additional import/axiom replay; none is silently declared to require new Kani if its owning job can compose existing cuts in Lean.\n'
 (E/'NLO_REMAINING.md').write_text(rem)
 return cs,paths,unowned
