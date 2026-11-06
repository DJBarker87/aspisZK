"""Fail closed: no ledger promotion before complete combined gate and review."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess
from NKW_report import report
E=Path(__file__).resolve().parent;P=E.parent/'ledger19-20261108';H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def raw(p):return p.read_bytes()if p.is_file()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def put(n,x):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/n
 if n=='NKW_LEDGER.json'or len(b)>20_000_000:Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(b)
required=J(E/'NKW_AUDIT_ROOTS.json')['roots'];results=[];disagreements=[];nonzero=[]
for i in range(30):
 d=J(E/f'NKW_audit/batch{i}/proof{i}.json');results+=d['results']
 if d['exit_status']:nonzero.append(f'NKW_L{i+9:03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required)==len({r['root']for r in results})==10538
assert {r['root']for r in results}==set(required)
assert [r['root']for r in disagreements]==['NHC_DecodeModel.decoder_error']
fx=J(E/'NKW_audit/fixtures/fixtures.json');oldfx=J(P/'NKN_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==oldfx['results']and len(fx['results'])==8
scan=[json.loads(l)for l in raw(E/'NKW_LOADED_scan.jsonl').decode().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan);assert J(E/'NKW_audit/scan/scan.json')['exit_status']==0
put('NKW_SCAN.json',dict(exit_status=0,modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,canonical_duplicate_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan),scanner='NFX method; NKN Driver module/path-only adaptation',attempt='NKW_L008',full_combined_import='NKW_COMBINED_IMPORT'))
rs=[json.loads(l)for l in(E/'NKW_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==len({r['attempt']for r in rs})==40
for r in rs:
 a=r['attempt'];rc=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'and(r['exit_status']==0 or a in nonzero)
 assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
resources=dict(scopes=40,complete_receipts=40,unused_scopes=0,kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),kani=0,extraction=0,aggregation16G_scopes=0,retained_nonzero_audit_exits=nonzero)
binary=J(E/'NKW_L006/NKW_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NKW_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean']);oldAudit=J(P/'NKN_AUDIT.json');assert H(canonical)==oldAudit['walker']['sha256'];(E/'NKW_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NKW_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert raw(E/'NKW_L006/sources/NKW_native'/n)==raw(P/'NKN_L006/sources/NKN_native'/n)
assert J(E/'NKW_PREDECESSOR_COMPARISON.json')['status']=='PASS'
assert J(E/'NKW_NATIVE_REVIEW.json')['status']=='PASS_READ_ONLY_RECEIPT_REVALIDATION'
assert J(E/'NKW_SOURCE_REVIEW.json')['status']=='PASS'and J(E/'NKW_OWNER_COMPARISON.json')['status']=='PASS'
assert J(E/'NKW_L039/receipt.json')['exit_status']==0 and J(E/'NKW_L040/receipt.json')['exit_status']==0
nkt=J(E/'NKW_NKT_COVERAGE.json');assert nkt['covered_rows']==551 and len(nkt['transparent_no_root_rows'])==2 and not nkt['admissible_candidate_roots_not_covered']and {r['root']for r in nkt['all_confirmed_batch_tree_dependencies']}=={r['root']for r in nkt['structural_dependency_statement_reviews']} and all(r['verdict']=='INSENSITIVE_FOR_RECORDED_ROW_CLAIM'for r in nkt['structural_dependency_statement_reviews'])
put('NKW_RESOURCES.json',resources)
put('NKW_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDING',full_composition_pass=True,combined='NKW_COMBINED_IMPORT',combined_attempt='NKW_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)",retained_nonzero_audit_exits=nonzero,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NKW_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NKW_WALKER_SOURCE.lean.txt',sha256=H(canonical),byte_identical=True,object_pins=actual,native_link_inputs_byte_identical_to_NKN=True),NKT_coverage='NKW_NKT_COVERAGE.json; F2/F3 explicitly OPEN',resources=resources,security_target_established=False,cold_release_replay=False))
basis=J(P/'NKN_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};review=J(E/'NKW_CANDIDATE_REVIEW.json');assert len(review['rows'])==10;changes=[];rejected=[]
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 if c['recommendation']=='KEEP_OPEN':
  rejected.append(dict(row=r['row'],provider=c['provider'],missing_clause=c['missing_clause'],supporting_roots=c['roots']));r['obligation']['NKW_rejected_candidate']=copy.deepcopy(rejected[-1]);continue
 assert c['recommendation']=='ADMIT_ONLY_AFTER_GATE'
 o=copy.deepcopy(r['obligation']);o['NKW_basis_obligation']=copy.deepcopy(r['obligation']);o['certificate']=c['certificate'];o['kernel_roots']=c['kernel_statements'];o['NKW_complete_clause_review']=c['original_clauses'];o['NKW_hypothesis_inventory']=c['hypothesis_inventory'];o['NKW_root_domain']=c['root_domain'];o['NKW_semantic_review']=c['review']
 primary=next(k for k in c['kernel_statements']if k['root']==c['primary_root'])
 r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module=primary['owner_module'],owner_role='canonical checked row packet',root_owners=[dict(root=k['root'],owner_module=k['owner_module'],obligation_statement_sha256=H(k['obligation_statement'].encode()))for k in c['kernel_statements']],evidence_dir='evidence/ledger20-20261109')
 c['gate_admitted']=True;changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',primary_root=c['primary_root'],owner_module=r['owner_module'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],domain=c['root_domain'],roots=r['root_owners']))
assert len(changes)==7 and len(rejected)==3
parent=J(E/'NKW_PARENT_CLAUSES.json')
for rid in parent['parents']:
 r=by[rid];o=r['obligation'];o['NKW_parent_basis_obligation']=copy.deepcopy(oldby[rid]['obligation']);o['NKW_explicit_child_domains']=[c for c in parent['clauses']if c['parent']==rid];o['caller_domain_obligations'] += [c['caller_clause']for c in parent['clauses']if c['parent']==rid]
for r in ledger['rows']:
 old=oldby[r['row']];assert old['canonical_callees']==r['canonical_callees']
 if r['obligation']!=old['obligation']:r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
for c in changes:c['complete_obligation_statement_hash']=by[c['row']]['obligation_statement_hash']
rt=[dict(item=c['provider']+'-RT'+c['row'].split(':')[1],row=c['row'],root=c['primary_root'],classification='ReviewedTranscription; P6/D188 option-A RECLASSIFICATION, never removal',scope='Actual frozen native callee/iteration cuts and SAME-domain full Result/ordered frame composition',provider=c['provider'])for c in changes]
ledger['reviewed_transcription_inventory']+=rt
reclass=dict(ruling='(bc)',classification='RECLASSIFIED, not removed',item='Aeneas emission fidelity / narrowed D188 extraction',definition='Faithful except explicit returns or ? in post-loop code merged into loop exit; body must be free of pattern or affected exits natively certified.',confirmed='NKT-F1 batch_tree:TX1:083/TX2:055 remain OPEN',coverage='NKW_NKT_COVERAGE.json',provenance='NKT-F2 OPEN:274emission blobs without recovered exact tool origin',root_provenance='NKT-F3 OPEN:TX1:059/TX2:040 inherited zero-root accessor packets; no newly validated credit')
ledger.setdefault('extraction_trust_reclassifications',[]).append(reclass)
for f in [dict(id='NKT-F2',status='OPEN',obligation=reclass['provenance']),dict(id='NKT-F3',status='OPEN',rows=['TX1:059','TX2:040'],obligation=reclass['root_provenance'])]:ledger.setdefault('open_findings',[]).append(f)
assert ledger['trust_rows']==basis['trust_rows']
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':560,'OPEN':39}
assert {r['row']for r in ledger['rows']if r['status']!=oldby[r['row']]['status']}=={c['row']for c in changes}
ledger.update(basis='NKN ledger19 plus7 NKW-gated candidates;3 remain OPEN with exact missing clauses',basis_delta='NKW_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NKW_LEDGER.json',ledger);put('NKW_LEDGER_DELTA.json',dict(basis='evidence/ledger19-20261108/NKN_LEDGER.json.xz',before=dict(CLOSED=553,QUALIFIED=0,OPEN=46),after=dict(CLOSED=560,QUALIFIED=0,OPEN=39),new_closed_rows=[c['row']for c in changes],new_count=7,rows=changes,no_double_count=True,no_other_status_change=True,explicit_parent_clause_updates=parent,added_edges=[],reviewed_transcription_additions=rt,extraction_trust_reclassification=reclass,trust_rows_changed=False,security_target_established=False,rejected_candidates=rejected,supporting_only=['NKK_ tx2-resume','NKE_ tx2-native9','NKS_ Pool inventory613ON/494outside599'],gate=[r['attempt']for r in rs]))
put('NKW_TRUST_INVENTORY.json',dict(runtime_cryptographic_rows_unchanged=True,runtime_rows_sha256=H(json.dumps(basis['trust_rows'],sort_keys=True).encode()),added_reviewed_transcription_items=rt,extraction_reclassification=reclass,removed=[],classification='Option-A P6/D188 RECLASSIFICATION, never removal',op38='quantified; no PDA value row',digest_error_slots=[43,44],RuntimePersistence='data-only',RuntimeCpiReadonlyEntry7='unused'))
review['status']='PASS_COMPLETE_REVIEW_AND_FULL_GATE_SEVEN_ADMITTED_THREE_OPEN';review['gate_pass']=True;put('NKW_CANDIDATE_REVIEW.json',review)
report(ledger,resources)
plan=f'''# NKW ledger20 status\n\nTarget not yet established. Thirteenth all-slices composition gate PASS:560 CLOSED /0 QUALIFIED /39 OPEN of599, versus NKN553/0/46. Seven admissions:NKM TX1:NGB006/NGB004/NGB002;NKI TX1:234/260/233;NKL TX1:084. Three candidates stay OPEN:TX1:235 lacks literal full emitted Result association;TX2:216/218 lack exact arbitrary-reservation Box allocation identity/effects. Complete missing clauses and support retained. Original edges/clauses retained;17 additive helper-own/unit clauses at parents, no unsubmitted parent credit.\n\nAll10538 required roots raw-audited in this combined environment, standard axioms only. Same optimized binary/eight fixtures PASS;NFX exit0 across{len(scan)}modules, zero dangling/canonical duplicate/incompatible owners/import defects. All10190 predecessor statements and owners unchanged; full selected closure/Aeneas pins retained. NHC_DecodeModel.decoder_error actual nonzero group exit and raw/collector disagreement retained under(ab\u0027)(3).\n\nNKM split route reviewed:universal arbitrary canonical-reply parent with full3/7event trace, one assumed-spec field boundary K026 plus valid zero-add control K028, Lean field law instantiation. K025/K027 timeouts excluded. Both error arms and singular-first order retained;fallback uses fixed inverse certificates. NKI234/260/233 preserve complete records/domains/frames;235 decoded four-cell result support is not promoted. NKL scanner exact Result/readonly frame/first rejection certified and(bc)-insensitive. NKP all6checkpoint/14master windows and mapped errors checked at SAME raw152/153 arguments;allocation identity and full outcome/post law remains missing despite unused universal Reservation binder.\n\nOnly trust inventory changes:seven ReviewedTranscription additions and(bc) extraction-fidelity RECLASSIFICATION, never removal. Confirmed NKT-F1 affects already OPEN batch_tree rows;every named credited root covered. NKT-F2 provenance for274emission blobs OPEN;NKT-F3 two inherited zero-root to_limbs certificates explicitly OPEN provenance, no new validation. Runtime/cryptographic trust rows byte-identical as data. K086 liveness/abort, production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING;NKS613ON/494outside599 inventory only. All named Pool joins OPEN/conditional as named.\n\n40/40serial scopes,0Kani/0extraction;each admission exit0 AND allowed:true;6Ghigh/8Gmax/swap0/tasks64,-M7000. Optional16G unused. Total wall{resources['wall_seconds']:.3f}s,peakRSS{resources['peak_rss_kib']}KiB,swaps0. Exact per-scope targets/revisions/source/dependencies/exit/wall/RSS/swap/axioms retained. No timeout/memory-kill/rerun, no cap increase. No shipped source or ELF rebuild trigger;inherited artifact pins only. Own cache/TMPDIR retained.\n\nFrozen revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387;frozen3;headline AspisR1.RPx_Deployed.deployed;L154 statement parameter;narrowedD188;100-bit PER-ATTEMPT/privacy/two-transaction contract unchanged. RuntimePersistence data-only;initial Pool seven fields;RuntimeCpiReadonlyEntry7 unused;op38 quantified,digest/error43/44. Entry/op9/native forest/Pool continuation,L187cold replay,L188artifact/extraction remain.\n'''
(E/'NKW_PLAN_STATUS.md').write_text(plan);(E/'NKW_HANDOFF.md').write_text(plan.replace('# NKW ledger20 status','# NKW ledger20 handoff')+'\nRead NKW_LEDGER_DELTA.json,NKW_CANDIDATE_REVIEW.json,NKW_PARENT_CLAUSES.json,NKW_AUDIT.json,NKW_SCAN.json,NKW_PHYSICAL.md,NKW_REMAINING.md. Seed NKW_EXPORT.json first then NKW_PATHS.json. This is a coherent focused composition, not a cold release replay. No push, sibling/session-A worktree edit, shipped-source/runtime trust change or key/account/fund/authority action.\n')
print(json.dumps(dict(status='PASS',closed=560,open=39,roots=len(required),modules=len(scan),scopes=40)))
