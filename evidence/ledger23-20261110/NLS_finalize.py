"""Admit exactly four candidates only after the complete ledger23 gate."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess
from NLS_report import report
E=Path(__file__).resolve().parent;P=E.parent/'ledger22-20261110';Q=E.parent/'terminal6-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
def put(n,x):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/n
 if n=='NLO_LEDGER.json'or len(b)>20000000:Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(b)
required=J(E/'NLS_AUDIT_ROOTS.json');results=[];disagreements=[];nonzero=[]
for i,group in enumerate(required['groups']):
 d=J(E/f'NLS_audit/batch{i}/proof{i}.json');assert [r['root']for r in d['results']]==group;results+=d['results']
 if d['exit_status']:nonzero.append(f'NLS_L{i+9:03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
 assert d['exit_status']==(1 if any(not r['equal']for r in d['results'])else 0)
assert len(results)==len(required['roots'])==len({r['root']for r in results})==11302
assert {r['root']for r in disagreements}=={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
fx=J(E/'NLS_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==J(P/'NLO_audit/fixtures/fixtures.json')['results']and len(fx['results'])==8
scan=J(E/'NLO_SCAN.json');assert scan['exit_status']==0 and not(scan['dangling']or scan['canonical_duplicate_owners']or scan['import_mismatches'])
rs=[json.loads(l)for l in(E/'NLS_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==len({r['attempt']for r in rs})==40
for r in rs:
 a=r['attempt'];rc=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'and(r['exit_status']==0 or a in nonzero)
 assert any(J(p)['free']>=40000000000 for p in E.glob(a+'-disk*.json'))
resources=dict(scopes=40,complete_receipts=40,unused_scopes=0,kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),kani=0,extraction=0,aggregation16G_scopes=0,retained_nonzero_audit_exits=nonzero)
binary=J(E/'NLS_L006/NLS_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NLS_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
assert J(E/'NLS_PREDECESSOR_COMPARISON.json')['status']=='PASS'
assert J(E/'NLS_SOURCE_OBJECT_REVIEW.json')['status']=='PASS_COMMITTED_SOURCE_HASHES_MATCH_SUCCESSFUL_COMPILES'
assert J(E/'NLS_OWNER_COMPARISON.json')['status']=='PASS'
assert J(E/'NLS_CLAUSE_MATRIX.json.xz')['status']=='PASS_COMPLETE_CLAUSE_REVIEW'
assert J(E/'NLS_FINAL_HOST.json')['status']=='PASS'
assert J(E/'NLS_NATIVE_REVIEW.json')['status']=='PASS'
canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean']);oldAudit=J(P/'NLO_AUDIT.json');assert H(canonical)==oldAudit['walker']['sha256'];(E/'NLS_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NLS_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert raw(E/'NLS_L006/sources/NLS_native'/n)==raw(P/'NLO_L006/sources/NLO_native'/n)
put('NLO_RESOURCES.json',resources)
put('NLO_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_COLLECTOR_FINDINGS',full_composition_pass=True,combined='NLS_COMBINED_IMPORT',combined_artifact='NLO_COMBINED_IMPORT.lean',combined_attempt='NLS_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(results),new_roots=128,raw_standard_axioms_only=True,all_required_raw_roots_present=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)/(ax2)",retained_nonzero_audit_exits=nonzero,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NLO_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NLS_WALKER_SOURCE.lean.txt',sha256=H(canonical),object_pins=actual,native_link_inputs_identical_to_NLO=True),resources=resources,security_target_established=False,cold_release_replay=False))
basis=J(P/'NLO_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};review=J(E/'NLS_CANDIDATE_REVIEW.json');assert len(review['rows'])==4;changes=[];matrix=J(E/'NLS_CLAUSE_MATRIX.json.xz')
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 o=copy.deepcopy(r['obligation']);o['NLS_basis_obligation']=copy.deepcopy(r['obligation']);o['certificate']=c['certificate'];o['kernel_roots']=c['kernel_statements'];o['NLS_complete_clause_review']=c['original_clauses'];o['NLS_clause_dispositions']=[v for v in matrix['clauses']if v['row']==r['row']];o['NLS_hypothesis_inventory']=c['hypothesis_inventory'];o['NLS_root_domain']=c['root_domain'];o['NLS_semantic_review']=c['review'];o['NLS_callee_occurrence_reviews']=[v for v in matrix['callee_occurrence_reviews']if v['parent']==r['row']]
 # Current caller obligations are discharged; historical copies remain untouched.
 for clause in o['caller_domain_obligations']:
  clause['status']='INTERNAL_DISCHARGED';clause['discharged_by']=c['primary_root']+'; '+c['review']
 for clause in o['inventory_domain_obligations']:
  clause['status']='CALLER_PROVENANCE_RETAINED';clause['discharged_by']='Local native association discharged by '+c['primary_root']+'; enclosing provenance carried by explicit NLS_root_domain at each parent.'
 primary=c['kernel_statements'][0]
 r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module=primary['owner_module'],owner_role='canonical checked row packet',root_owners=[dict(root=k['root'],owner_module=k['owner_module'],obligation_statement_sha256=H(k['obligation_statement'].encode()))for k in c['kernel_statements']],evidence_dir='evidence/ledger23-20261110')
 c['gate_admitted']=True;changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',primary_root=c['primary_root'],owner_module=r['owner_module'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],domain=c['root_domain'],roots=r['root_owners']))
parent=J(E/'NLS_PARENT_CLAUSES.json')
for rid in parent['parents']:
 r=by[rid];o=r['obligation'];o['NLS_parent_basis_obligation']=copy.deepcopy(oldby[rid]['obligation']);o['NLS_explicit_child_domains']=[c for c in parent['clauses']if c['parent']==rid];o['caller_domain_obligations'] += [c['caller_clause']for c in parent['clauses']if c['parent']==rid]
for r in ledger['rows']:
 old=oldby[r['row']];assert old['canonical_callees']==r['canonical_callees']
 if r['obligation']!=old['obligation']:r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
for c in changes:c['complete_obligation_statement_hash']=by[c['row']]['obligation_statement_hash']
rt=[dict(item='NLH-RT-'+c['row'].split(':')[1],row=c['row'],root=c['primary_root'],classification='ReviewedTranscription; existing P6/D188 option-A RECLASSIFICATION, never removal',scope='Frozen native parent/child cuts; full SAME-argument canonical Result/chronological effects/frame/abort association',provider='NLH')for c in changes]
ledger['reviewed_transcription_inventory']+=rt;assert ledger['trust_rows']==basis['trust_rows']
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':580,'OPEN':19}
assert {r['row']for r in ledger['rows']if r['status']!=oldby[r['row']]['status']}=={c['row']for c in changes}
ledger.update(basis='NLO ledger22 plus4 NLS-gated NLH candidates;599 rows and every edge retained',basis_delta='NLO_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NLO_LEDGER.json',ledger);put('NLO_LEDGER_DELTA.json',dict(basis='evidence/ledger22-20261110/NLO_LEDGER.json.xz',before=dict(CLOSED=576,QUALIFIED=0,OPEN=23),after=dict(CLOSED=580,QUALIFIED=0,OPEN=19),new_closed_rows=[c['row']for c in changes],new_count=4,rows=changes,no_double_count=True,no_other_status_change=True,explicit_parent_clause_updates=parent,added_edges=[],reviewed_transcription_additions=rt,trust_rows_changed=False,security_target_established=False,rejected_candidates=[],supporting_only=['NKV_','NLL_','NLJ_ RowSpec_094','NLK_'],rulings=['bf own-input domains recorded verbatim at every actual caller; parent proves SAME arguments','aq2/bf3 no child Result/success/endpoint/global/headline/physical-state premise','bd/be state-event folds; generic package lemmas SUPPORT only','ab3/ax2 raw walk authoritative; both collector disagreements retained']))
review['status']='PASS_ALL_4_GATE_ADMITTED';put('NLS_CANDIDATE_REVIEW.json',review)
report(ledger,resources)
raw_gate=J(E/'NLS_RAW_GATE.json');raw_gate.update(status='PASS',full_gate_pending=False,full_gate='PASS');put('NLS_RAW_GATE.json',raw_gate)
plan=f'''# Ledger23 status

Target not yet established. Sixteenth all-slices composition gate PASS: 580 CLOSED / 0 QUALIFIED / 19 OPEN of 599 (ledger22:576/0/23). Admitted NLH TX1:261 semantic_packed,237 composition_parts,263 terminal_parts,256 r0::Public::terminal_qm31. No other status or edge changes. All722 recursive original clause records reviewed and retained;33 verbatim own-input clauses plus four inherited inventory-context clauses retained at parents;11 actual child occurrences checked. CLOSED deterministic308 remains237's child, never an oracle. Caller136 remains OPEN and must establish256's explicit Public/claims/point/challenge domains.

THIS combined import passed with11302 roots raw-standard-only,128 new roots, the same optimized binary/eight fixtures and NFX exit0 across{scan['modules']} modules. Zero dangling/canonical duplicate/incompatible owners/import defects;{scan['cached_replicas']} identical serialized cache replicas retained, not conflicting semantic owners. All11174 predecessor statements/owners unchanged;78 candidate sources match successful compile hashes. Both collector disagreements NHC_DecodeModel.decoder_error and NKR_ScheduleExt.transition retained under(ab')(3)/(ax2); raw walks use only propext/Classical.choice/Quot.sound. Private rows_ext stays in raw inventory; combined-import generator emits module imports only, no private source-name lookup.

NLH261 instantiates232/233/250/228/229 on consecutive actual canonical arrays/selectors.237 derives261's amount bound from its own precheck and gathers all child domains at SAME arguments; consumes CLOSED218 and deterministic308 internally.263 retains all six channels before the nine-event arithmetic suffix;256 proves the full84 gather frame, SAME255 public projection and both Rust Result map arms, with no suffix on error/abort. Own input clauses comply with(bf)(2); no child success/Result/endpoint/free Ops/Run premise in any row root. Generic cut-packaging lemmas are SUPPORT only. Native23 positive/control pairs (46receipts/28distinct retained input hashes) revalidated read-only: frozen graph/lock, deployed features, selected source and exact KMX patch unchanged. Older off-path Pool source is excluded from selected native closures; no Pool parity/bridge/ELF credit.

Trust inventory: four NLH ReviewedTranscription additions under existing option-A P6/D188 are reclassifications, never removals. No runtime/cryptographic trust-row change. K086 liveness/abort; production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING. Pool397ON/278new/D30/6owners/3held inventory only; named producers/guards/sites OPEN, conditional read-to-settlement model retained. Poolb936275465/ELFe0e49c34…;121f3e29 historical. No verifier row depends on Pool ELF.

40/40 serial scopes,0Kani/0extraction. All admission exit0 AND allowed:true,hostfree>=40GB,6Ghigh/8Gmax/swap0/tasks64,Lean-M7000. Optional16G unused. Total wall{resources['wall_seconds']:.3f}s;peakRSS{resources['peak_rss_kib']}KiB;swaps0. Exact targets/commands/revisions/hashes/dependencies/metrics/axioms retained in NLO_ATTEMPTS.jsonl and per-scope receipts. No timeout,memory kill,unchanged rerun or cap increase. Own client adaptations preserve validation; shared infrastructure untouched. Cache/TMPDIR retained.

Frozen verifier4bb3b3f5;frozen3;headline AspisR1.RPx_Deployed.deployed;L154 statement parameter;narrowedD188;100-bit PER-ATTEMPT/privacy/two-transaction contract unchanged. RuntimePersistence data-only;initial Pool seven fields only;RuntimeCpiReadonlyEntry7 unused;PDAop38 quantified,digest/error43/44. Entry/op9/native forest/Pool continuation,L187cold replay,L188artifact/extraction,NKT-F2/F3provenance remain. Focused coherent cached composition,not cold release replay. No shipped-source change or ELF rebuild trigger;pins inherited,not reproduced.
'''
(E/'NLO_PLAN_STATUS.md').write_text(plan)
(E/'NLO_HANDOFF.md').write_text(plan.replace('status','handoff',1)+'\nRead NLO_LEDGER_DELTA.json,NLS_CANDIDATE_REVIEW.json,NLS_CLAUSE_MATRIX.json.xz,NLS_PARENT_CLAUSES.json,NLO_AUDIT.json,NLO_SCAN.json,NLO_PHYSICAL.md,NLO_REMAINING.md. Seed NLO_EXPORT.json first,then NLO_PATHS.json; import NLS_COMBINED_IMPORT (NLS_MODULE_MAP.json), since NLO_COMBINED_IMPORT.lean is the required receipt filename and the imported NLO module is ledger22. All evidence lives in evidence/ledger23-20261110. No push,sibling/session-A worktree edit,shipped-source/runtime trust change or key/account/fund/authority action.\n')
# Requested output names are aliases of NLS-owned evidence, never a conflicting Lean module.
for old,new in [('NLS_ATTEMPTS.jsonl','NLO_ATTEMPTS.jsonl'),('NLS_EXPORT.json','NLO_EXPORT.json'),('NLS_PATHS.json','NLO_PATHS.json')]: (E/new).write_bytes((E/old).read_bytes())
print(json.dumps(dict(status='PASS',closed=580,open=19,roots=len(results),modules=scan['modules'],scopes=40)))
