from pathlib import Path
import json,lzma,hashlib,collections,subprocess,copy,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'ledger17-20261108';H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if n=='NKH_LEDGER.json'or len(raw)>20_000_000:
  Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(H(raw)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(raw)
required=J(E/'NKH_AUDIT_ROOTS.json')['roots'];results=[];disagreements=[];nonzero=[]
for i in range(30):
 d=J(E/f'NKH_audit/batch{i}/proof{i}.json');results+=d['results']
 if d['exit_status']:nonzero.append(f'NKH_L{min(i+9 if i<16 else i+10,38):03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required)==len({r['root']for r in results})and{r['root']for r in results}==set(required)
assert[r['root']for r in disagreements]==['NHC_DecodeModel.decoder_error']
fx=J(E/'NKH_audit/fixtures/fixtures.json');oldfx=J(P/'NKC_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==oldfx['results']and len(fx['results'])==8
scan=[json.loads(l)for l in(E/'NKH_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
assert J(E/'NKH_audit/scan/scan.json')['exit_status']==0
put('NKH_SCAN.json',dict(exit_status=0,modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan),scanner='NFX method; NKC_Driver module/root/path-only adaptation',attempt='NKH_L008',full_combined_import='NKH_COMBINED_IMPORT',canonical_duplicate_owners=0))
rs=[json.loads(l)for l in(E/'NKH_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==40 and len({r['attempt']for r in rs})==40
assert rs[-1]['attempt']=='NKH_L040'and rs[-1]['exit_status']==0
for r in rs:
 a=r['attempt'];ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 if a=='NKH_L025':
  assert r['exit_status'] is None;continue
 rc=J(E/a/'receipt.json');assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'and rc['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-ledger18-20261108/NKH_target'
 assert r['exit_status']==0 or a in nonzero or a=='NKH_L039'
resources=dict(scopes=len(rs),kinds=dict(collections.Counter(r['kind']for r in rs)),submitted_scopes=40,complete_receipts=39,unused_scopes=0,wall_seconds=sum(r['wall_seconds']for r in rs if r['wall_seconds'] is not None),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs if r['peak_rss_kib'] is not None),swaps=sum(int(r['swaps'])for r in rs if r['swaps'] is not None),unresolved_metrics=['NKH_L025 ENOSPC child exit/wall/peakRSS/swap unavailable'],resubmission=dict(attempt='NKH_L026',resubmits='NKH_L025',reason='Lead host repair environment change'),retained_tool_nonzero_exits=[dict(attempt=r['attempt'],target=r['module'],exit=r['exit_status'])for r in rs if r['exit_status'] is not None and r['exit_status']],kani=0,extraction=0,aggregation16G_scopes=0)
binary=J(E/'NKH_L006/NKH_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NKH_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
oldAudit=J(P/'NKC_AUDIT.json');canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'],cwd=R);assert H(canonical)==oldAudit['walker']['sha256'];(E/'NKH_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NKH_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert(E/'NKH_L006/sources/NKH_native'/n).read_bytes()==(P/'NKC_L006/sources/NKC_native'/n).read_bytes()
put('NKH_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDING',full_composition_pass=True,combined='NKH_COMBINED_IMPORT',combined_attempt='NKH_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)",retained_nonzero_audit_exits=nonzero,retained_nonzero_compile_exits=['NKH_L039'],diagnostic_repair='NKH_REVIEW_REPAIR.json',same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NKH_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NKH_WALKER_SOURCE.lean.txt',byte_identical=True,sha256=H(canonical),object_pins=actual,driver_diffs=['NKH_Driver.diff','NKH_ProofDriver.diff'],native_link_inputs_byte_identical_to_NKC=True),resources=resources,security_target_established=False,cold_release_replay=False))
put('NKH_RESOURCES.json',resources)
assert J(E/'NKH_PREDECESSOR_COMPARISON.json')['status']=='PASS'
assert J(E/'NKH_NATIVE_REVIEW.json')['status']=='PASS_READ_ONLY_RECEIPT_REVALIDATION'
assert J(E/'NKH_COVERAGE.json')['status']=='PASS_READ_ONLY_ALL_ARMS_AND_FULL_RETURN_REVIEW'

assert J(E/'NKH_OWNER_COMPARISON.json')['status']=='PASS'
review=J(E/'NKH_CANDIDATE_REVIEW.json');assert len(review['rows'])==28 and review['no_double_count']
assert J(E/'NKH_L039/receipt.json')['exit_status']==1
assert J(E/'NKH_audit/review-close/review.json')['exit_status']==0
assert J(E/'NKH_MATCHER_OWNERS.json')['status']=='PASS'
assert len(J(E/'NKH_KERNEL_STATEMENTS.json.xz'))==10066
assert all(not c['missing_kernel_roots']for c in review['rows'])
basis=J(P/'NKC_LEDGER.json.xz');ledger=copy.deepcopy(basis);oldby={r['row']:r for r in basis['rows']};by={r['row']:r for r in ledger['rows']};changes=[]
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 o=copy.deepcopy(r['obligation']);o['basis_obligation']=copy.deepcopy(r['obligation']);o['certificate']=c['certificate'];o['kernel_roots']=c['kernel_statements'];o['NKH_complete_clause_review']=c['original_clauses'];o['NKH_hypothesis_inventory']=c['hypothesis_inventory'];o['NKH_root_domain']=c['root_domain'];o['NKH_semantic_review']=c['review']
 primary=next(k for k in c['kernel_statements']if k['root']==c['primary_root'])
 r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module=primary['owner_module'],owner_role='canonical checked row packet',root_owners=[dict(root=x['root'],owner_module=x['owner_module'],obligation_statement_sha256=H(x['obligation_statement'].encode()))for x in c['kernel_statements']],evidence_dir='evidence/ledger18-20261108')
 changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',primary_root=c['primary_root'],owner_module=r['owner_module'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],domain=c['root_domain'],roots=r['root_owners'],caller_clauses='All original clauses retained verbatim; NKH_PARENT_CLAUSES.json records the exact own-domain and unit-context requirements at every actual parent.'))
parent=J(E/'NKH_PARENT_CLAUSES.json')
for rid in parent['parents']:
 r=by[rid];o=r['obligation'];o['NKH_parent_basis_obligation']=copy.deepcopy(oldby[rid]['obligation']);o['NKH_explicit_child_domains']=[c for c in parent['clauses']if c['parent']==rid]
 o['caller_domain_obligations'] += [c['caller_clause']for c in parent['clauses']if c['parent']==rid]
for c in changes:
 r=by[c['row']];r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode());c['complete_obligation_statement_hash']=r['obligation_statement_hash']
for rid in parent['parents']:
 r=by[rid];r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
# Complementary generalized current-word law admitted only after the full gate.
sup=J(E/'NKH_SUPPLEMENT_REVIEW.json');assert sup['no_NoBad_history_proof_persistence_or_success_premise']
supplement=copy.deepcopy(basis['supplemental_child_obligations'][0]);assert supplement['status']=='OPEN'
supplement.update(status='CLOSED',owner='NKH gated NJU generalized current-word finish packet',evidence='evidence/ledger18-20261108/NKH_SUPPLEMENT_REVIEW.json',kernel_roots=[sup[k]for k in ['primary_root','ported_root','caller_root','rejection_root']],domain=sup['domain'],complementary_law=sup['complementary_law'])
ledger['supplemental_child_obligations']=[supplement]
sup.update(status='CLOSED',missing=None,gate='NKH full composition gate');put('NKH_SUPPLEMENT_REVIEW.json',sup)
assert by['TX1:202']['function']in by['TX1:069']['canonical_callees']
rt=J(E/'NKH_COVERAGE.json')['trust_additions']
ledger['reviewed_transcription_inventory']=basis.get('reviewed_transcription_inventory',[])+rt
put('NKH_TRUST_INVENTORY.json',dict(runtime_cryptographic_rows_unchanged=True,added_reviewed_transcription_items=rt,removed=[],classification='P6/D188 option-A RECLASSIFICATION, never removal',runtime_rows_sha256=H(json.dumps(basis['trust_rows'],sort_keys=True).encode()),boundary='Reader ONLY N4/16/32 backing1768 U11/S2; Transcript ONLY deployed SolanaDigest; digest/error43/44 retained'))
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':542,'OPEN':57};assert ledger['trust_rows']==basis['trust_rows']
ledger.update(basis='NKC ledger17 plus28 NKH-gated NJZ/NKD/NJX occurrences and NJU off-domain115 supplement; original clauses retained',basis_delta='NKH_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NKH_LEDGER.json',ledger)
put('NKH_LEDGER_DELTA.json',dict(schema_version=1,basis='evidence/ledger17-20261108/NKC_LEDGER.json.xz',before=dict(CLOSED=514,QUALIFIED=0,OPEN=85),after=dict(CLOSED=542,QUALIFIED=0,OPEN=57),new_closed_rows=[c['row']for c in changes],new_count=28,rows=changes,no_double_count=True,no_other_status_change=True,gate=[r['attempt']for r in rs],explicit_parent_clause_updates=parent,new_child_obligations=[],supplement_status=supplement,retained_child_obligations=[supplement],inventory_edge_reclassifications=[],reviewed_transcription_additions=rt,trust_rows_changed=False,security_target_established=False,supporting_imports_without_credit=['NJL same-argument helpers unchanged in NKC','NJU source-only resume/common roots receive no row credit'],rejected_candidates=[]))
review['status']='PASS_COMPLETE_STATEMENTS_EMISSION_OWNERS_AND_FULL_GATE';review['gate_pass']=True
for c in review['rows']:
 c.pop('admissible_pending_gate',None);c['gate_admitted']=True;c['admission_blocker']=None
put('NKH_CANDIDATE_REVIEW.json',review)
from NKH_report import report
report(ledger,resources)
print(json.dumps(dict(status='PASS',closed=542,open=57,qualified=0,roots=len(required),modules=len(scan),scopes=len(rs))))
