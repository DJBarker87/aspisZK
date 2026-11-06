from pathlib import Path
import json,lzma,hashlib,copy,subprocess,re
E=Path(__file__).resolve().parent
read=lambda p:lzma.open(p).read().decode() if p.suffix=='.xz' else p.read_text() if p.exists() else lzma.open(str(p)+'.xz').read().decode()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(read(p))
ats=[json.loads(l)for l in(E/'NKG_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({a['attempt']for a in ats})==len(ats)
assert sum(a['kind']=='kani'for a in ats)<=80
assert sum(a['kind'] in ['lean','link','audit']for a in ats)<=90
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for a in ats:
 rc=load(E/a['attempt']/'receipt.json');ad=load(E/(a['attempt']+'-admission.json'))
 assert ad['exit']==0 and ad['reservation']['allowed']is True,a['attempt']
 assert rc['limits']==limits and str(rc['swaps'])=='0',a['attempt']
 assert rc['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-poseidon-state-20261108/NKG_target'
 assert all(k in rc for k in ['module','command','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps'])
for a in ['NKG_L051','NKG_L052','NKG_L053','NKG_L054']:assert load(E/a/'receipt.json')['exit_status']==0
inventory=load(E/'NKG_PROOF_INVENTORY.json');raw=load(E/'NKG_L054_validation/NKG_RESULTS.json');fixtures=load(E/'NKG_L052_validation/NKG_RESULTS.json')
assert sorted(r['root']for r in raw['results'])==sorted(inventory['roots'])
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw['results'])
assert len(fixtures['results'])==8 and all(r['equal']for r in fixtures['results'])
assert all(r['walked_axioms']for r in fixtures['results'][:4]) and all(not r['walked_axioms']for r in fixtures['results'][4:])
assert raw['binary']['sha256']==fixtures['binary']['sha256']
scan=[json.loads(l)for l in read(E/'NKG_LOADED_scan.jsonl').splitlines()]
assert len(scan)>15963 and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match']for r in scan)
triples=[[1,2,3],[4,5],[6,7],[8,9],[13,11,12],[14,15,16],[17,18,19],[32,33,34],[26,27,28],[35,36,37],[38,39,40],[41,42,43],[44,45,46],[29,30,31],[47,48],[49,50],[51,52]]
nativepins={}
for pair in triples:
 hashes=[]
 for i,n in enumerate(pair):
  a=f'NKG_K{n:03}';rc=load(E/a/'receipt.json');log=read(E/a/'stdout.log');v=E/(a+'_validation')
  assert rc['exit_status']==(0 if i==0 else 1),a
  assert 'timed out'not in log.lower(),a
  assert ('VERIFICATION:- SUCCESSFUL'in log or 'VERIFICATION SUCCESSFUL'in log) if i==0 else ('VERIFICATION:- FAILED'in log or 'VERIFICATION FAILED'in log),a
  g=load(v/'NHR_GRAPH_CHECK.json');tg=load(v/'NKG_TARGET_GRAPH.json');lk=load(v/'NKG_LOCK.json');inp=load(v/'NKG_INPUTS.json')
  assert g['graph_matches_frozen'] and not g['added'] and not g['edge_errors']
  assert tg['graph_matches_frozen'] and not tg['edge_errors'] and tg['lock_unchanged']
  assert lk['unchanged'] and lk['before']==lk['after']==g['lock_before']==g['lock_after']
  assert inp['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert '--locked'not in inp['native_command'] and rc['env']['CARGO_NET_OFFLINE']=='true'
  hashes.append(inp['harness_sha256']);nativepins[a]=dict(receipt_sha256=sha(E/a/'receipt.json'),inputs_sha256=sha(v/'NKG_INPUTS.json'),harness_sha256=inp['harness_sha256'])
 assert len(set(hashes))==1,('unmatched complete harness source',pair)
assert load(E/'NKG_SOURCE_ASSOCIATION.json')['projected_group_and_four_segments_exact']
assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs','Cargo.lock']).returncode==0
baseline_file=E.parent/'ledger17-20261108/NKC_LEDGER.json.xz';base=load(baseline_file);original=load(E/'NKG_BASELINE_ROWS.json')
byfunc={r['function']:r for r in base['rows'] if r['status']=='CLOSED'}
actual_mul='crates/aspis-core/src/field.rs::PreparedQm31Multiplier::mul';assert actual_mul not in byfunc
spec={
'TX1:321':('AspisR1.NKG_ColumnsPacket.source','canonical SAME three QM31 weights and three width16 M31 columns; constants <2147483647',[[1,2],[1,3],[4,5],[6,7],[8,9]],['AspisR1.NKG_ColumnTotal.step_total','AspisR1.NKG_ColumnReply.result','AspisR1.NKG_ColumnLoop.source']),
'TX1:324':('AspisR1.NKG_InternalPacket.source','canonical SAME complete width16 state and selector array',[[13,11],[13,12],[4,5]],['AspisR1.NKG_HelperDomains.internal','AspisR1.NKG_InternalMaps.weights','AspisR1.NKG_InternalMaps.constants_even','AspisR1.NKG_InternalMaps.constants_odd','AspisR1.NKG_InternalSource.result']),
'TX1:323':('AspisR1.NKG_FullPacket.source','canonical SAME complete width16 state and selector array; all six ROM columns derived internally',[[14,15],[14,16],[4,5]],['AspisR1.NKG_HelperDomains.full','AspisR1.NKG_FullSource.result']),
'TX1:308':('AspisR1.NKG_OraclePacket.source','canonical SAME openings z/succ_z/xor12_z, selector.local[16] and selector.block; exact fixed input/public-tree carrier retained',[[17,18],[17,19],[32,33],[32,34],[35,36],[35,37],[38,39],[38,40],[41,42],[41,43],[44,45],[44,46],[26,27],[26,28],[29,30],[29,31],[47,48],[49,50],[51,52],[4,5]],['AspisR1.NKG_LowFrame.full','AspisR1.NKG_LowFrame.internal','AspisR1.NKG_PreludeFrame.result','AspisR1.NKG_GroupFrame.result','AspisR1.NKG_GroupRaw.value','AspisR1.NKG_CellTotal.cell','AspisR1.NKG_OracleChoices.ready','AspisR1.NKG_OracleSource.result'])}
functions=[];packets=[]
for row in original:
 key=row['row'];root,domain,pairs,support=spec[key];assert row['status']=='OPEN'
 clauses=[]
 for clause in row['obligation']['caller_domain_obligations']:
  c=copy.deepcopy(clause);callee=c.get('callee');c.update(disposition='DISCHARGED at actual SAME use / conservative alternatives visibly retained',discharged_by=[root]+support)
  if callee:
   if callee in byfunc:c['closed_child']=dict(row=byfunc[callee]['row'],root_owners=byfunc[callee]['root_owners'])
   else:
    owned=next((r for r in original if r['function']==callee),None);assert owned is not None,callee;c['closed_child_candidate']=dict(row=owned['row'],root=spec[owned['row']][0],admit_bottom_up_in_same_gate=True)
   c['resolution']='Frozen typed QM31/Prepared call structure, exact source-token association and complete-root domain laws. Heuristic CM31/M31/WideExact alternatives are retained as conservative source-type alternatives, not silently removed; field internals compose through their CLOSED child.'
  else:c['resolution']='Safe constructor/map/fold/from_fn/index operation under pinned Aeneas std (au), executed within native cuts where reached; exact finite source control and KMX copy controls retained.'
  clauses.append(c)
 extra=[]
 if key=='TX1:308':extra=[dict(function=actual_mul,baseline_row=None,disposition='Field-product rule A: Lean-discharged emitted PreparedQm31Multiplier.mul law; no invented CLOSED child row',domain='PreparedFor SAME constructor block and canonical SAME sum reply',discharged_by=['AspisR1.NKG_AfterTotal.result','AspisR1.NKG_OracleChoices.ready','AspisR1.FIv_PreparedTotal.mul'],native_pairs=[['NKG_K044','NKG_K045'],['NKG_K044','NKG_K046']],inventory_resolution='Original prepared_block.mul heuristic lists generic field-carrier alternatives; actual receiver is PreparedQm31Multiplier. This additive exact-source supplement retains every original edge; baseline ledger unchanged.')]
 f=dict(rows=[key],function=row['function'],route='(y)/(ai)(5)/(ad)/(aq)/(aq)(5)/(au) direct P6 hybrid',root_domain=domain,native_pairs=[[f'NKG_K{n:03}'for n in p]for p in pairs],lean_roots=[root]+support,complete_carrier=True,premise_policy='Only own canonical fixed input carrier and reviewed parent native cuts; every child Result/domain discharged internally; no arbitrary Ops, caller success/output/Run or independent child endpoint premise',trust='P6/D188 option A RECLASSIFICATION; existing Std/allocator/ABI/runtime/source-to-ELF realization retained; no trust row added or removed')
 functions.append(f)
 packets.append(dict(row=key,function=row['function'],frozen_revision=base['frozen_revision'],frozen_body_sha256=row['frozen_body_sha256'],original_obligation_statement_hash=row['obligation_statement_hash'],original_inventory=row,root=root,caller_clauses=clauses,supplemental_actual_callees=extra,root_hypothesis_inventory=dict(own_domain=domain,reviewed_cuts={'TX1:321':['NKG_ColumnCuts.Trace/Step'],'TX1:324':['NKG_HelperCuts.Internal'],'TX1:323':['NKG_HelperCuts.Full'],'TX1:308':['NKG_PreludeFrame.Cut (including native LowTrace and constructor/branch cuts)','NKG_GroupFrame.Frame for each of four original groups','NKG_OracleCuts.Output']}[key],extra_logical_hypotheses=[],child_results='Derived by literal CLOSED child laws at SAME logged arguments, not fields left to caller',standing_trust_retained=True),complete_result_and_frame=True,admission='Local NKC+deployed combined import, NFX exit0 and raw ax2 standard axioms PASS; authoritative next-ledger credit pending'))
closed=dict(frozen_revision=base['frozen_revision'],headline='AspisR1.RPx_Deployed.deployed',functions=functions,admission='One local combined gate PASS; proposed CLOSED candidates, credit waits for next authoritative ledger gate',status='CLOSED candidate packets under recorded own domains; not authoritative ledger credit',target_established=False)
counts=copy.deepcopy(base['counts']);delta=dict(baseline='evidence/ledger17-20261108/NKC_LEDGER.json.xz',baseline_sha256=sha(baseline_file),baseline_counts=counts,proposed_rows=['TX1:321','TX1:324','TX1:323','TX1:308'],authoritative_ledger_changed=False,credit_pending=True,expected_counts_if_all_four_admitted=dict(CLOSED=518,QUALIFIED=0,OPEN=81,total=599),exact_source_edge_supplement=actual_mul,target_established=False)
audit=dict(target_established=False,headline=closed['headline'],combined_audits_used=1,combined_audit_limit=2,gate='PASS',combined='NKG_L051',fixtures='NKG_L052',scan='NKG_L053',raw='NKG_L054',modules=len(scan),roots=len(raw['results']),fixtures_count=8,same_fixture_and_raw_binary=True,proof_binary_sha256=raw['binary']['sha256'],coherence_defects=0,standard_axioms_only=True,collectors_equal=True,cached_compatible_replicas=sum(len(s.get('cached_replicas',[]))if isinstance(s.get('cached_replicas'),list)else int(s.get('cached_replicas',0))for s in scan),next_ledger_credit_pending=True,cold_release_replay=False)
resources=dict(attempts=len(ats),kinds={k:sum(a['kind']==k for a in ats)for k in ['kani','lean','link','audit']},budget_used=dict(kani=sum(a['kind']=='kani'for a in ats),lean_link_audit=sum(a['kind']in['lean','link','audit']for a in ats),extraction=0),budget_limit=dict(kani=80,lean_link_audit=90,extraction=1),wall_seconds=sum(a['wall_seconds']for a in ats),peak_rss_kib=max(int(a['peak_rss_kib'])for a in ats),swaps=sum(int(a['swaps'])for a in ats),limits=limits,receipts=[dict(attempt=a['attempt'],target=a['module'],kind=a['kind'],exit_status=a['exit_status'],wall_seconds=a['wall_seconds'],peak_rss_kib=a['peak_rss_kib'],swaps=a['swaps'],source_revision=a.get('source_revision'),receipt=a['full_receipt'])for a in ats])
for name,obj in [('NKG_CLOSED.json',closed),('NKG_ROW_PACKETS.json',packets),('NKG_LEDGER_DELTA.json',delta),('NKG_AUDIT.json',audit),('NKG_RESOURCE_SUMMARY.json',resources),('NKG_NATIVE_PINS.json',nativepins)]:
 (E/name).write_text(json.dumps(obj,indent=2)+'\n')
# Every actual new theorem source is pinned to its successful receipt.
for m,pin in inventory['modules'].items():assert sha(E/'NKG_lean'/f'{m}.lean')==pin['source_sha256']
print(json.dumps(dict(gate='PASS',candidate_rows=4,raw_roots=len(raw['results']),modules=len(scan),native_positive=17,native_controls=28,budget=resources['budget_used'])))
