"""No promotion unless this combined environment passes every required gate."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess
from NLG_report import report
E=Path(__file__).resolve().parent;P=E.parent/'ledger20-20261109';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):return p.read_bytes()if p.is_file()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
def put(n,x):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/n
 if n=='NLG_LEDGER.json'or len(b)>20_000_000:Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(b)
required=J(E/'NLG_AUDIT_ROOTS.json')['roots'];results=[];disagreements=[];nonzero=[]
for i in range(30):
 d=J(E/f'NLG_audit/batch{i}/proof{i}.json');assert [r['root']for r in d['results']]==J(E/'NLG_AUDIT_ROOTS.json')['groups'][i];results+=d['results']
 if d['exit_status']:nonzero.append(f'NLG_L{i+9:03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required)==len({r['root']for r in results})==10720
assert {r['root']for r in results}==set(required)
assert [r['root']for r in disagreements]==['NHC_DecodeModel.decoder_error']
assert len(nonzero)==1 and J(E/nonzero[0]/'receipt.json')['exit_status']==1
fx=J(E/'NLG_audit/fixtures/fixtures.json');oldfx=J(P/'NKW_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==oldfx['results']and len(fx['results'])==8
scan=[json.loads(l)for l in raw(E/'NLG_LOADED_scan.jsonl').decode().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan);assert J(E/'NLG_audit/scan/scan.json')['exit_status']==0
put('NLG_SCAN.json',dict(exit_status=0,modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,canonical_duplicate_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan),scanner='NFX method; unchanged NKW Driver except NLG module/path adaptation',attempt='NLG_L008',full_combined_import='NLG_COMBINED_IMPORT'))
rs=[json.loads(l)for l in(E/'NLG_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==len({r['attempt']for r in rs})==40
for r in rs:
 a=r['attempt'];rc=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'and(r['exit_status']==0 or a in nonzero)
 assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
resources=dict(scopes=40,complete_receipts=40,unused_scopes=0,kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),kani=0,extraction=0,aggregation16G_scopes=0,retained_nonzero_audit_exits=nonzero)
binary=J(E/'NLG_L006/NLG_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NLG_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
oldAudit=J(P/'NKW_AUDIT.json');canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean']);assert H(canonical)==oldAudit['walker']['sha256'];(E/'NLG_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NLG_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert raw(E/'NLG_L006/sources/NLG_native'/n)==raw(P/'NKW_L006/sources/NKW_native'/n)
assert J(E/'NLG_PREDECESSOR_COMPARISON.json')['status']=='PASS'
for file,status in [('NLG_NATIVE_REVIEW.json','PASS_READ_ONLY_RECEIPT_REVALIDATION'),('NLG_SOURCE_REVIEW.json','PASS'),('NLG_OWNER_COMPARISON.json','PASS'),('NLG_SOURCE_OBJECT_REVIEW.json','PASS_COMMITTED_SOURCE_HASHES_MATCH_SUCCESSFUL_COMPILES'),('NLG_CLAUSE_MATRIX.json','PASS_COMPLETE_CLAUSE_REVIEW'),('NLG_OCCURRENCES.json','PASS_ALL_ORIGINAL_OCCURRENCES')]:assert J(E/file)['status']==status
assert J(E/'NLG_L039/receipt.json')['exit_status']==0 and J(E/'NLG_L040/receipt.json')['exit_status']==0
put('NLG_RESOURCES.json',resources)
put('NLG_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDING',full_composition_pass=True,combined='NLG_COMBINED_IMPORT',combined_attempt='NLG_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),new_roots=len(required)-10538,all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)",retained_nonzero_audit_exits=nonzero,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NLG_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NLG_WALKER_SOURCE.lean.txt',sha256=H(canonical),byte_identical=True,object_pins=actual,native_link_inputs_byte_identical_to_NKW=True),resources=resources,security_target_established=False,cold_release_replay=False))
basis=J(P/'NKW_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};review=J(E/'NLG_CANDIDATE_REVIEW.json');assert len(review['rows'])==4;changes=[];matrix=J(E/'NLG_CLAUSE_MATRIX.json')['clauses']
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 assert c['recommendation']=='ADMIT_ONLY_AFTER_GATE'
 o=copy.deepcopy(r['obligation']);o['NLG_basis_obligation']=copy.deepcopy(r['obligation']);o['certificate']=c['certificate'];o['kernel_roots']=c['kernel_statements'];o['NLG_complete_clause_review']=c['original_clauses'];o['NLG_clause_dispositions']=[v for v in matrix if v['row']==r['row']];o['NLG_hypothesis_inventory']=c['hypothesis_inventory'];o['NLG_root_domain']=c['root_domain'];o['NLG_semantic_review']=c['review'];o['NLG_previous_rejection']='NKW missing clause superseded by named complete Result/allocator roots; original rejection retained as historical evidence'
 primary=next(k for k in c['kernel_statements']if k['root']==c['primary_root'])
 r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module=primary['owner_module'],owner_role='canonical checked row packet',root_owners=[dict(root=k['root'],owner_module=k['owner_module'],obligation_statement_sha256=H(k['obligation_statement'].encode()))for k in c['kernel_statements']],evidence_dir='evidence/ledger21-20261110')
 c['gate_admitted']=True;changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',primary_root=c['primary_root'],owner_module=r['owner_module'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],domain=c['root_domain'],roots=r['root_owners']))
assert len(changes)==4
parent=J(E/'NLG_PARENT_CLAUSES.json')
for rid in parent['parents']:
 r=by[rid];o=r['obligation'];o['NLG_parent_basis_obligation']=copy.deepcopy(oldby[rid]['obligation']);o['NLG_explicit_child_domains']=[c for c in parent['clauses']if c['parent']==rid];o['caller_domain_obligations'] += [c['caller_clause']for c in parent['clauses']if c['parent']==rid]
for r in ledger['rows']:
 old=oldby[r['row']];assert old['canonical_callees']==r['canonical_callees']
 if r['obligation']!=old['obligation']:r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
for c in changes:c['complete_obligation_statement_hash']=by[c['row']]['obligation_statement_hash']
rt=[dict(item=c['provider']+'-RT'+c['row'].split(':')[1],row=c['row'],root=c['primary_root'],classification='ReviewedTranscription; existing P6/D188 option-A RECLASSIFICATION, never removal',scope='Actual frozen native parent/child cuts and SAME-domain full Result/chronological effects/frame association',provider=c['provider'])for c in changes]
ledger['reviewed_transcription_inventory']+=rt
assert ledger['trust_rows']==basis['trust_rows']
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':564,'OPEN':35}
assert {r['row']for r in ledger['rows']if r['status']!=oldby[r['row']]['status']}=={c['row']for c in changes}
ledger['pins']=dict(verifier_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',verifier_scope=['crates/','programs/r1-cost-probe','Cargo.lock'],pool_source='b936275465600469312d1f058cdc91ea2a11f3dc',default_elf='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet_elf='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',pool_elf='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc',historical_pool_elf='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548',pins_inherited_not_reproduced=True,no_verifier_row_depends_on_pool_elf=True)
ledger['Pool_status']=dict(inventory_only=True,source='evidence/pool-inventory2-20261109/NKZ_INVENTORY.json',ON=397,new_to_basis=278,D=30,guard_owners=6,held_sites=3,production_closed=0,owner_aj_a='PENDING',K086='liveness/abort; production reachability/exclusion UNPROVED')
ledger.update(basis='NKW ledger20 plus4 NLG-gated candidates; original599 rows and every edge retained',basis_delta='NLG_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NLG_LEDGER.json',ledger);put('NLG_LEDGER_DELTA.json',dict(basis='evidence/ledger20-20261109/NKW_LEDGER.json.xz',before=dict(CLOSED=560,QUALIFIED=0,OPEN=39),after=dict(CLOSED=564,QUALIFIED=0,OPEN=35),new_closed_rows=[c['row']for c in changes],new_count=4,rows=changes,no_double_count=True,no_other_status_change=True,explicit_parent_clause_updates=parent,added_edges=[],reviewed_transcription_additions=rt,trust_rows_changed=False,security_target_established=False,rejected_candidates=[],supporting_only=['NKO_','NKQ_','NLA_','NLB_ conditional065','NLD_','NKX_ legacy removal','NKZ_ inventory397/278/D30/guard6/held3'],rulings=['(bd) fold-first ONE state; intermediate child-conditional lemmas earn no row credit','(be) exact typed RowSpec when absent; SDK wrapper transcription under existing std item, NLF shared support'],gate=[r['attempt']for r in rs]))
put('NLG_TRUST_INVENTORY.json',dict(runtime_cryptographic_rows_unchanged=True,runtime_rows_sha256=H(json.dumps(basis['trust_rows'],sort_keys=True).encode()),added_reviewed_transcription_items=rt,removed=[],classification='Option-A P6/D188 RECLASSIFICATION, never removal',op38='quantified; no PDA value row',digest_error_slots=[43,44],RuntimePersistence='data-only',RuntimeCpiReadonlyEntry7='unused',be='Existing std interpretation for SDK wrapper support, no new runtime/crypto row',bc='Existing extraction fidelity reclassification retained;235 unaffected tuple tail; batch tree OPEN; NKT-F2/F3 OPEN provenance'))
review['status']='PASS_COMPLETE_REVIEW_AND_FULL_GATE_FOUR_ADMITTED';review['gate_pass']=True;put('NLG_CANDIDATE_REVIEW.json',review)
report(ledger,resources)
plan=f'''# NLG ledger21 status

Target not yet established. Fourteenth all-slices composition gate PASS:564 CLOSED /0 QUALIFIED /35 OPEN of599, versus NKW560/0/39. Admitted NKU TX2:124 and NKY TX1:235, TX2:216/218. No other row status or edge changes. All76 original candidate call clauses reviewed and retained. Fourteen additive parent clauses include proof57607/public0..1880 at TX2:065 AND upward064/241/240/221/213; no discharge or parent promotion here.

All10720 required roots freshly raw-audited in THIS combined import, standard axioms only. Same optimized binary/eight fixtures PASS; NFX exit0 across{len(scan)} modules, zero dangling/canonical duplicate/incompatible owners/import defects. All10538 predecessor statements/owners unchanged;108 actually loaded candidate sources match successful compile hashes. Full selected closure/Aeneas pins retained. NHC_DecodeModel.decoder_error original group exit1/raw-collector discrepancy preserved under(ab')(3).

NKU one parent State/fold covers all45 top-level and74 nested Reader occurrences, full Result/chronological log, SAME Reservation and every Err/fail/div prefix. Native Prepared uses complete constructor assertions, never variant-onlyK045. Incoming native proof/public extent remains caller-owned. NKY235 supplies literal full emitted-body port2+2array Result association, every packet witness; post-loop tuple tail unaffected by(bc). NKY216/218 consume arbitrary SAME Reservation at sole Box::new, exact actual carrier, allocator post and caller-visible heap inside ONE Result; no allocation-success premise. Fresh-block-or-abort/std/P6 interpretation remains retained trust, not totality or removal.

Only trust inventory changes:four ReviewedTranscription additions under existing option-A P6/D188. No runtime or cryptographic row changes. Rulings(bd) fold-first and(be) typed child packet/SDK wrapper-under-std recorded. K086 liveness/abort; production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING. NKZ397ON/278new/D30/6owners/3held inventory only; named Pool producers and all retained guards/sites remain OPEN, conditional read-to-settlement model retained. Pool pin updated to e0e49c34… at b936275465;121f3e29… historical. No verifier row depends on Pool ELF.

40/40 serial Lean/link/audit scopes,0Kani/0extraction; each admission exit0 AND allowed:true and hostfree>=40GB. All6Ghigh/8Gmax/swap0/tasks64, Lean-M7000; optional16G unused. Total wall{resources['wall_seconds']:.3f}s, peakRSS{resources['peak_rss_kib']}KiB, swaps0. Exact targets, commands, source revisions/hashes, dependency pins, exits, timings, RSS, swap and axioms in NLG_ATTEMPTS.jsonl/per-scope receipts. No timeout/memory-kill/unchanged rerun or cap increase. Shared launcher/shim/reservation untouched; own reader fixes documented. Own cache/TMPDIR retained.

Frozen verifier4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; frozen3; headline AspisR1.RPx_Deployed.deployed; L154 statement parameter; narrowedD188;100-bit PER-ATTEMPT/privacy/two-transaction contract unchanged. RuntimePersistence data-only; initial Pool seven fields only; RuntimeCpiReadonlyEntry7 unused; op38 quantified, digest/error43/44. Entry/op9/native forest/Pool continuation,L187cold replay,L188artifact/extraction and NKT-F2/F3provenance remain. This is focused coherent composition, not a cold release replay. No shipped-source change or ELF rebuild trigger; pins inherited, not reproduced.
'''
(E/'NLG_PLAN_STATUS.md').write_text(plan);(E/'NLG_HANDOFF.md').write_text(plan.replace('# NLG ledger21 status','# NLG ledger21 handoff')+'\nRead NLG_LEDGER_DELTA.json,NLG_CANDIDATE_REVIEW.json,NLG_CLAUSE_MATRIX.json,NLG_PARENT_CLAUSES.json,NLG_AUDIT.json,NLG_SCAN.json,NLG_PHYSICAL.md,NLG_REMAINING.md. Seed NLG_EXPORT.json first, then NLG_PATHS.json. No push, sibling/session-A worktree edit, shipped-source/runtime trust change or key/account/fund/authority action.\n')
print(json.dumps(dict(status='PASS',closed=564,open=35,roots=len(required),modules=len(scan),scopes=40)))
