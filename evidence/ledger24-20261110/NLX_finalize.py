"""Admit only TX2:065 after the complete ledger24 gate."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess
from NLX_report import report
E=Path(__file__).resolve().parent;P=E.parent/'ledger23-20261110';Q=E.parent/'tx2-common2-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
def put(n,x):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/n
 if n=='NLX_LEDGER.json'or n=='NLX_KERNEL_STATEMENTS.json'or len(b)>20_000_000:
  Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(b)
required=J(E/'NLX_AUDIT_ROOTS.json');results=[];disagreements=[];nonzero=[]
group_plan=J(E/'NLX_AUDIT_GROUPS.json')['required']
for entry in group_plan:
 i=entry['group'];group=required['groups'][i]
 d=J(E/f'NLX_audit/{entry["mode"]}/proof{i}.json');assert [r['root']for r in d['results']]==group;results+=d['results']
 if d['exit_status']:nonzero.append(entry['scope'])
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
 assert d['exit_status']==(1 if any(not r['equal']for r in d['results'])else 0)
assert len(results)==len(required['roots'])==len({r['root']for r in results})==11370
assert {r['root']for r in disagreements}=={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
fx=J(E/'NLX_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==J(P/'NLS_audit/fixtures/fixtures.json')['results']and len(fx['results'])==8
scanrows=[json.loads(l)for l in raw(E/'NLX_LOADED_scan.jsonl').decode().splitlines()]
sr=J(E/'NLX_audit/scan/scan.json');assert sr['exit_status']==0
scan=dict(status='PASS',exit_status=0,attempt='NLX_L007',scanner='NFX canonical complete private loaded environment scan',combined='NLX_COMBINED_IMPORT',modules=len(scanrows),dangling=sum(len(r['dangling'])for r in scanrows),canonical_duplicate_owners=sum(len(r['duplicate_owners'])for r in scanrows),import_mismatches=sum(not r['imports_match']for r in scanrows),cached_replicas=sum(len(r.get('cached_replicas',[]))for r in scanrows),identical_replicas_are_not_semantic_duplicate_owners=True)
assert not(scan['dangling']or scan['canonical_duplicate_owners']or scan['import_mismatches']);put('NLX_SCAN.json',scan)
statements={}
for line in raw(E/'NLX_L008/stdout.log').decode().splitlines():
 if 'NLX_OWNER 'in line:
  x=json.loads(line.split('NLX_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x
old=J(P/'NLS_KERNEL_STATEMENTS.json.xz');assert set(statements)==set(required['roots'])and all(statements.get(n)==v for n,v in old.items())
assert statements['NLT_CompleteRoot.root']['owner_module']=='NLT_CompleteRoot';put('NLX_KERNEL_STATEMENTS.json',statements);put('NLX_OWNER_COMPARISON.json',dict(status='PASS',previous=len(old),identical=len(old),new=len(statements)-len(old),wrong=[]))
rs=[json.loads(l)for l in(E/'NLX_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==len({r['attempt']for r in rs})==40
for r in rs:
 a=r['attempt'];rc=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'and(r['exit_status']==0 or a in nonzero or(a=='NLX_L023'and r['exit_status']==124))
 assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
resources=dict(scopes=40,complete_receipts=40,unused_scopes=0,kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),kani=0,extraction=0,aggregation16G_scopes=0,retained_nonzero_audit_exits=nonzero,retained_timeout_attempts=['NLX_L023'],max_cgroup_memory_peak_bytes=max(J(E/r['attempt']/'receipt.json')['cgroup_memory_peak_bytes']for r in rs))
binary=J(E/'NLX_L006/NLX_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NLX_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
assert J(E/'NLX_PREDECESSOR_COMPARISON.json')['status']=='PASS'and J(E/'NLX_FINAL_HOST.json')['status']=='PASS'
assert J(E/'NLX_SOURCE_REVIEW.json')['status']=='PASS'and J(E/'NLX_CLAUSE_MATRIX.json.xz')['status']=='PASS_COMPLETE_CLAUSE_REVIEW'
review=J(E/'NLX_CANDIDATE_REVIEW.json');assert not review['withdrawn_root_credit']and review['primary_root']=='NLT_CompleteRoot.root'
canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean']);oldAudit=J(P/'NLO_AUDIT.json');assert H(canonical)==oldAudit['walker']['sha256'];(E/'NLX_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NLX_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert raw(E/'NLX_L005/sources/NLX_native'/n)==raw(P/'NLS_L006/sources/NLS_native'/n)
put('NLX_RESOURCES.json',resources)
put('NLX_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_COLLECTOR_FINDINGS',full_composition_pass=True,combined='NLX_COMBINED_IMPORT',combined_attempt='NLX_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(results),new_roots=len(statements)-len(old),raw_standard_axioms_only=True,all_required_raw_roots_present=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)/(ax2)",retained_nonzero_audit_exits=nonzero,retained_timeout_attempts=['NLX_L023'],active_raw_groups=len(group_plan),root_set_unchanged_after_split=True,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NLX_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NLX_WALKER_SOURCE.lean.txt',sha256=H(canonical),object_pins=actual,native_link_inputs_identical_to_ledger23=True),resources=resources,security_target_established=False,cold_release_replay=False))
basis=J(P/'NLO_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};r=by['TX2:065'];assert r['status']=='OPEN'and r['obligation_statement_hash']==review['basis_obligation_statement_hash']
assert all(next(z for z in ledger['rows']if z['transaction']=='TX2'and z['function']==c)['status']=='CLOSED'for c in r['canonical_callees'])
matrix=J(E/'NLX_CLAUSE_MATRIX.json.xz');o=copy.deepcopy(r['obligation']);o['NLX_basis_obligation']=copy.deepcopy(r['obligation']);o['NLX_complete_clause_review']=matrix;o['NLX_hypothesis_inventory']=review['hypothesis_inventory'];o['NLX_root_domain']=review['own_argument_clauses'];o['kernel_roots']=[statements['NLT_CompleteRoot.root']];o['NLX_same_argument_checks']=review['same_argument_checks'];o['NLX_NLT_F1_disposition']='NLT_Root.root WITHDRAWN for credit; complete root includes independent C04 stopped arm, no returned child reply or native suffix; ideal source suffix explicit'
cert=o['certificate'];cert.update(bridge_status='CLOSED',composed_status='CLOSED',no_credit_reason='Historical rejection superseded only for TX2:065 by the complete NLX gate; original certificate retained in NLX_basis_obligation',NLX_provider='NLT',NLX_root='NLT_CompleteRoot.root',NLX_gate='PASS',NLX_route='direct hybrid P6 native cuts, CLOSED child instantiation and Lean parent continuation fold',NLX_trust='Existing option-A P6/D188 native semantic transport, std/allocator/runtime/ABI/source-to-ELF retained; reclassification never removal',NLX_no_new_native_or_extraction_run=True)
for clause in o['caller_domain_obligations']:
 clause['status']='INTERNAL_DISCHARGED';clause['discharged_by']='NLT_CompleteRoot.root; NLX_CLAUSE_MATRIX.json.xz names exact SAME-call proof and retained input provenance'
for clause in o['inventory_domain_obligations']:
 clause['status']='INTERNAL_DISCHARGED_WITH_CALLER_PROVENANCE_RETAINED';clause['discharged_by']='NLT_CompleteRoot.root; complete Result/error/abort parent fold with three own-input clauses recorded at064, not a successful-input premise'
r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module='NLT_CompleteRoot',owner_role='canonical checked complete row packet; independent stopped C04 included',root_owners=[dict(root='NLT_CompleteRoot.root',owner_module='NLT_CompleteRoot',obligation_statement_sha256=H(statements['NLT_CompleteRoot.root']['obligation_statement'].encode()))],evidence_dir='evidence/ledger24-20261110')
parents=J(E/'NLX_PARENT_CLAUSES.json');assert parents['parents']==['TX2:064'];par=by['TX2:064'];assert par['status']=='OPEN';par['obligation']['NLX_parent_basis_obligation']=copy.deepcopy(oldby['TX2:064']['obligation']);par['obligation']['NLX_explicit_child_domains']=parents['clauses']
for c in parents['clauses']:par['obligation']['caller_domain_obligations'].append(dict(id='NLX-bf:TX2:064:TX2:065:'+c['name'],caller=par['function'],callee=r['function'],required=c['required'],name=c['name'],classification=c['classification'],status='OPEN',discharged_by=None,reason='Original arguments; Root0/root1 cross-transaction provenance belongs064 and is NOT discharged by065'))
for row in ledger['rows']:
 prior=oldby[row['row']];assert prior['canonical_callees']==row['canonical_callees']
 if row['obligation']!=prior['obligation']:row['obligation_statement_hash']=H(json.dumps(row['obligation'],sort_keys=True,separators=(',',':')).encode())
rt=dict(item='NLT-TX2:065-native-contract-semantic-transport',row='TX2:065',root='NLT_CompleteRoot.root',classification='existing P6/D188 option-A native contract semantic transport RECLASSIFICATION, never removal',scope='SAME original continuation with C01/C04/C07, resolved and independently stopped C04 outcomes; original own-input bf2 caller clauses',provider='NLT')
ledger.setdefault('native_transport_reclassifications',[]).append(rt)
# Carry the lead-added runtime item only; do not retroactively attribute it to a closed root.
assert not any(t['id']=='RuntimeCpiAccountView'for t in basis['trust_rows'])
added=dict(id='RuntimeCpiAccountView',status='ADDED-LEAD-20261110',medium='trust row',ruling='Stream C(c-a)',scope='One returning Pool invoke/invoke_signed: admitted keys absent from instruction metas keep data incl length/lamports/owner; meta keys also in passed infos reflect callee final data/lamports/owner.',excluded='No CPI success, token/system semantics, readonly entry, rent/rollback/stack-height, key/flag/handle/Rc/borrow-counter stability or return-data law; exact metas/infos and cell separation remain native obligations.',direct_closed_rows=[],evidence=['design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md','docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md'],note='Carry lead addition read-only; soundness-side only, not privacy trust; no new runtime adoption by this job.')
ledger['trust_rows'].append(added);assert ledger['trust_rows'][:-1]==basis['trust_rows'];assert ledger['extraction_trust_reclassifications']==basis['extraction_trust_reclassifications']
ledger['NLX_inventory_notes']='NLX_INVENTORY_NOTES.md: inherited stale OPEN labels are historical, not current status; NKT-F2/F3 remain OPEN'
ledger['NLX_pool_read_only_context']=dict(source='evidence/pool-ledger1-20261110/PCE_LEDGER.json.xz',new_closed=15,new_open=263,new_total=278,shared=119,ON=397,on_guard_owners_closed=0,on_guard_owners=3,promotions_here=0)
counts=dict(collections.Counter(x['status']for x in ledger['rows']));assert counts=={'CLOSED':581,'OPEN':18};assert {x['row']for x in ledger['rows']if x['status']!=oldby[x['row']]['status']}=={'TX2:065'}
ledger.update(basis='ledger23 NLO_LEDGER (NLS gate) plus NLX-gated NLT_CompleteRoot.root only;599 rows and every edge retained',basis_delta='NLX_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NLX_LEDGER.json',ledger)
put('NLX_LEDGER_DELTA.json',dict(basis='evidence/ledger23-20261110/NLO_LEDGER.json.xz',basis_uncompressed_sha256=(P/'NLO_LEDGER.json.sha256').read_text().strip(),before=dict(CLOSED=580,QUALIFIED=0,OPEN=19),after=dict(CLOSED=581,QUALIFIED=0,OPEN=18),new_closed_rows=['TX2:065'],new_count=1,rows=[dict(row='TX2:065',previous_status='OPEN',status='CLOSED',primary_root='NLT_CompleteRoot.root',owner_module='NLT_CompleteRoot',basis_obligation_statement_hash=review['basis_obligation_statement_hash'],complete_obligation_statement_hash=r['obligation_statement_hash'],domain=review['own_argument_clauses'])],withdrawn_root='NLT_Root.root',withdrawn_root_credit=False,explicit_parent_clause_updates=parents,added_edges=[],removed_edges=[],no_other_status_change=True,no_double_count=True,reviewed_transcription_additions=[],native_transport_reclassifications=[rt],trust_inventory_additions=[added],trust_inventory_reclassifications=ledger['extraction_trust_reclassifications'],trust_inventory_removals=[],runtime_changes_beyond_recording_lead_addition=False,cryptographic_trust_changes=False,pool_promotions=[],security_target_established=False))
review.update(status='PASS_COMPLETE_ROOT_GATE_ADMITTED',gate_admitted=True,kernel_statement=statements['NLT_CompleteRoot.root']);put('NLX_CANDIDATE_REVIEW.json',review)
report(ledger,resources)
plan=f'''# NLX ledger24 status

Target not yet established. Seventeenth all-slices composition gate PASS:581 CLOSED /0 QUALIFIED /18 OPEN of599; ledger23:580/0/19. Only TX2:065 is promoted, through NLT_CompleteRoot.root. NLT_Root.root is withdrawn under NLT-F1 and gets no credit. Complete obligation, all312 recursive clause records and43 source/compiler snapshots reviewed. Same actual parent continuation, SAME C01/C04/C07 arguments, all resolved Results and independent stopped-C04 prefix are retained; no returned reply or native suffix on the stopped arm. Every other cut/domain is in(aq)(2) inventory, not a new endpoint/child-success premise.

Three Prop inputs are exactly proof.val.length=57607, pub.val.length≤1880, NLP_InputDomain.Root0 ck proof, all(bf)(2) on ORIGINAL inputs and recorded verbatim at OPEN caller TX2:064. Root0/root1 cross-transaction checkpoint/proof provenance remains064, requiring persistence AND proof-digest/writer binding; not discharged here.

Combined import NLX_COMBINED_IMPORT (NLS ledger23 + NLT + AspisR1.RPx_Deployed.deployed) passed. All{len(results)} roots raw ax2 standard-only;{len(statements)-len(old)} new roots; same optimized proof binary/eight fixtures. NFX scan exit0 across{scan['modules']} modules; zero dangling/canonical duplicate/incompatible owners/import defects;{scan['cached_replicas']} identical serialized cache replicas retained. All{len(old)} predecessor statements/owners unchanged. Two inherited collector disagreements retained under(ab')(3)/(ax2); raw walk authoritative, only propext/Classical.choice/Quot.sound. No credit without the full gate.

Physical distances recomputed from every canonical edge: entry(ao)(3)(b)40CLOSED/13OPEN of53; native forest(c)541CLOSED/5OPEN of546. Shortest TX1 spine6OPEN/5edges; TX2 spine5OPEN/6edges. Live owners NLQ/NLR/NLU/NLV/NLW and four paused unowned adapter rows are listed in NLX_PHYSICAL.md. Stream C PCE is read-only:15/278 new helpers CLOSED,263 OPEN,119shared,397ON; all3ON guard owners and P1..P4/prefix/read-to-settlement remain OPEN. No Pool promotion.

Trust inventory: RuntimeCpiAccountView ADDED-LEAD-20261110 carried per(c-a); no closed row uses it. Extraction narrowing(bc) and native contract semantic transport are RECLASSIFICATIONS, never removals. All prior runtime/cryptographic items retained. RuntimeCpiReadonlyEntry7 PENDING/UNUSED; RuntimePersistence data-only; initial Pool admission seven fields only; digest/error43/44, PDA38 quantified. K086 liveness/abort, production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING. Frozen3, L154 statement parameter, narrowedD188,100-bit PER-ATTEMPT/privacy/two-transaction contract unchanged.

40/40 serial scopes,0Kani/0extraction; all admission exit0 AND allowed:true, hostfree>=40GB, MemoryHigh6G/MemoryMax8G/swap0/tasks64, Lean-M7000; optional16GiB unused. Total scope wall{resources['wall_seconds']:.3f}s, peakRSS{resources['peak_rss_kib']}KiB, swaps0. Exact targets/status/wall/RSS/swap/revision/source+dependency hashes/axioms in NLX_ATTEMPTS.jsonl and per-scope receipts. Contention waits retained, never launched on refusal. L023 timed out at180.003s after319/379 walks without final batch receipt; zero credit from that attempt. Batch14 was split190/189 and batch15 proactively split; three cheap adjacent pairs preserve40scope budget and all11370 roots. Timeout receipt/cgroup peak and first unfinished root are in NLX_TIMEOUT.json. No memory kill, cap increase, timeout increase or unchanged timed-out-shape replay. Own client adapted from ledger23; shared infrastructure unchanged.

Focused coherent cached composition, not cold release replay or ELF reproduction. L187/L188/source-to-ELF/extraction/tool provenance and Pool actual execution remain obligations. No shipped file changed; no rebuild trigger. Inherited pins default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc /b936275465; frozen crates/programs-r1/Cargo.lock4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. No sibling/session-A worktree/key/account/fund/authority actions or push.
'''
(E/'NLX_PLAN_STATUS.md').write_text(plan);(E/'NLX_HANDOFF.md').write_text(plan.replace('status','handoff',1)+'\nRead NLX_LEDGER_DELTA.json, NLX_CANDIDATE_REVIEW.json, NLX_HYPOTHESES.md, NLX_PHYSICAL.md, NLX_REMAINING.md, NLX_AUDIT.json, NLX_SCAN.json, NLX_INVENTORY_NOTES.md and NLX_VALIDATION.json. Retained export in NLX_EXPORT.json; prepend it to NLX_PATHS.json and import NLX_COMBINED_IMPORT. Own cache/TMPDIR retained; all imported object hashes recorded. Stages committed locally; no push.\n')
print('NLX full composition gate PASS;581 CLOSED/0 QUALIFIED/18 OPEN;'+str(scan['modules'])+' modules;11370 roots')
