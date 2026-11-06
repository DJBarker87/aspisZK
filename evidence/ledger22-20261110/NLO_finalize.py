"""Promote only after THIS coherent import, raw ax2, fixtures and NFX gate."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess
from NLO_report import report
E=Path(__file__).resolve().parent;P=E.parent/'ledger21-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):return p.read_bytes()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
def put(n,x):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/n
 if n=='NLO_LEDGER.json'or len(b)>20_000_000:Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(b)
required=J(E/'NLO_AUDIT_ROOTS.json');results=[];disagreements=[];nonzero=[]
for i,group in enumerate(required['groups']):
 d=J(E/f'NLO_audit/batch{i}/proof{i}.json');assert [r['root']for r in d['results']]==group;results+=d['results']
 if d['exit_status']:nonzero.append(f'NLO_L{i+9:03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required['roots'])==len({r['root']for r in results})==11174
assert {r['root']for r in disagreements}=={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
fx=J(E/'NLO_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==J(P/'NLG_audit/fixtures/fixtures.json')['results']and len(fx['results'])==8
scan=J(E/'NLO_SCAN.json');assert scan['exit_status']==0 and not scan['dangling'] and not scan['canonical_duplicate_owners']and not scan['import_mismatches']
rs=[json.loads(l)for l in(E/'NLO_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==len({r['attempt']for r in rs})==40
for r in rs:
 a=r['attempt'];rc=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'and(r['exit_status']==0 or a in nonzero)
 assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
resources=dict(scopes=40,complete_receipts=40,unused_scopes=0,kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),kani=0,extraction=0,aggregation16G_scopes=0,retained_nonzero_audit_exits=nonzero)
binary=J(E/'NLO_L006/NLO_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NLO_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
assert J(E/'NLO_PREDECESSOR_COMPARISON.json')['status']=='PASS'
assert J(E/'NLO_SOURCE_OBJECT_REVIEW.json')['status']=='PASS_COMMITTED_SOURCE_HASHES_MATCH_SUCCESSFUL_COMPILES'
assert J(E/'NLO_OWNER_COMPARISON.json')['status']=='PASS'
assert J(E/'NLO_CLAUSE_MATRIX.json')['status']=='PASS_COMPLETE_CLAUSE_REVIEW'
assert J(E/'NLO_FINAL_HOST.json')['status']=='PASS'
canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean']);oldAudit=J(P/'NLG_AUDIT.json');assert H(canonical)==oldAudit['walker']['sha256'];(E/'NLO_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NLO_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert raw(E/'NLO_L006/sources/NLO_native'/n)==raw(P/'NLG_L006/sources/NLG_native'/n)
put('NLO_RESOURCES.json',resources)
put('NLO_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_COLLECTOR_FINDINGS',full_composition_pass=True,combined='NLO_COMBINED_IMPORT',combined_attempt='NLO_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(results),new_roots=454,raw_standard_axioms_only=True,all_required_raw_roots_present=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)/(ax2)",retained_nonzero_audit_exits=nonzero,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NLO_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NLO_WALKER_SOURCE.lean.txt',sha256=H(canonical),object_pins=actual,native_link_inputs_identical_to_NLG=True),resources=resources,security_target_established=False,cold_release_replay=False))
basis=J(P/'NLG_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};review=J(E/'NLO_CANDIDATE_REVIEW.json');assert len(review['rows'])==12;changes=[];matrix=J(E/'NLO_CLAUSE_MATRIX.json')['clauses']
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 o=copy.deepcopy(r['obligation']);o['NLO_basis_obligation']=copy.deepcopy(r['obligation']);o['certificate']=c['certificate'];o['kernel_roots']=c['kernel_statements'];o['NLO_complete_clause_review']=c['original_clauses'];o['NLO_clause_dispositions']=[v for v in matrix if v['row']==r['row']];o['NLO_hypothesis_inventory']=c['hypothesis_inventory'];o['NLO_root_domain']=c['root_domain'];o['NLO_semantic_review']=c['review']
 primary=next(k for k in c['kernel_statements']if k['root']==c['primary_root'])
 r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module=primary['owner_module'],owner_role='canonical checked row packet',root_owners=[dict(root=k['root'],owner_module=k['owner_module'],obligation_statement_sha256=H(k['obligation_statement'].encode()))for k in c['kernel_statements']],evidence_dir='evidence/ledger22-20261110')
 c['gate_admitted']=True;changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',primary_root=c['primary_root'],owner_module=r['owner_module'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],domain=c['root_domain'],roots=r['root_owners']))
parent=J(E/'NLO_PARENT_CLAUSES.json')
for rid in parent['parents']:
 r=by[rid];o=r['obligation'];o['NLO_parent_basis_obligation']=copy.deepcopy(oldby[rid]['obligation']);o['NLO_explicit_child_domains']=[c for c in parent['clauses']if c['parent']==rid];o['caller_domain_obligations'] += [c['caller_clause']for c in parent['clauses']if c['parent']==rid]
for s in parent['support']:
 for rid in s['rows']:by[rid]['obligation'].setdefault('NLO_support_only',[]).append(s)
for r in ledger['rows']:
 old=oldby[r['row']];assert old['canonical_callees']==r['canonical_callees']
 if r['obligation']!=old['obligation']:r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
for c in changes:c['complete_obligation_statement_hash']=by[c['row']]['obligation_statement_hash']
rt=[dict(item='NKR-RT-'+c['row'].split(':')[1],row=c['row'],root=c['primary_root'],classification='ReviewedTranscription; existing P6/D188 option-A RECLASSIFICATION, never removal',scope='Frozen native parent/child cuts; full SAME-argument canonical Result/chronological effects/frame association',provider='NKR')for c in changes if c['provider']=='NKR']
rt.append(dict(item='NKL-RT-batch_tree',rows=[c['row']for c in changes if c['provider']=='NLN'],provider='NLL/NKV/NLN',classification='ReviewedTranscription; existing P6/D188 option-A RECLASSIFICATION, never removal',scope='Full native returning Result (including Err Parse/Merkle), SAME mutable arrays/ordered histories/first rejection/abort prefix; own-input-domain universal packets under bf'))
ledger['reviewed_transcription_inventory']+=rt;assert ledger['trust_rows']==basis['trust_rows']
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':576,'OPEN':23}
assert {r['row']for r in ledger['rows']if r['status']!=oldby[r['row']]['status']}=={c['row']for c in changes}
ledger.update(basis='NLG ledger21 plus12 NLO-gated candidates;599 rows and every edge retained',basis_delta='NLO_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NLO_LEDGER.json',ledger);put('NLO_LEDGER_DELTA.json',dict(basis='evidence/ledger21-20261110/NLG_LEDGER.json.xz',before=dict(CLOSED=564,QUALIFIED=0,OPEN=35),after=dict(CLOSED=576,QUALIFIED=0,OPEN=23),new_closed_rows=[c['row']for c in changes],new_count=12,rows=changes,no_double_count=True,no_other_status_change=True,explicit_parent_clause_updates=parent,added_edges=[],reviewed_transcription_additions=rt,trust_rows_changed=False,security_target_established=False,rejected_candidates=[],supporting_only=['NLC_','NLF_ SDK borrow','NKV_','NLL_','NLE_ source extent/range'],rulings=['bf own-input callee domains recorded verbatim at every named caller occurrence; parent proves SAME arguments','aq2/bf3 no child result/success/endpoint/global/headline/physical-state premise','ab3/ax2 raw walk authoritative; both collector disagreements retained']))
review['status']='PASS_ALL_12_GATE_ADMITTED';put('NLO_CANDIDATE_REVIEW.json',review)
raw_audit=J(E/'NLO_RAW_AUDIT.json');raw_audit['full_gate_pending_final_closure']=False;raw_audit['full_gate']='PASS';put('NLO_RAW_AUDIT.json',raw_audit)
report(ledger,resources)
plan=f'''# NLO ledger22 status

Target not yet established. Fifteenth all-slices composition gate PASS: 576 CLOSED / 0 QUALIFIED / 23 OPEN of599 (NLG564/0/35). Admitted NKR TX1:225/232/251/250/220/218 and NLN TX2:055/054/053, TX1:083/082/081. No other status/edge changes. All176 original clauses reviewed and retained;74 additive parent/occurrence clauses recorded, including verbatim bf own-input clauses at TX2:065 C04 and TX1:094/087. No unsubmitted parent promotion. CLOSED deterministic308 remains237's child, never an oracle.

THIS combined import passed with11174 roots raw-standard-only, same optimized binary/eight fixtures and NFX exit0 across{scan['modules']} modules, zero dangling/canonical duplicate/incompatible owners/import defects. All10720 predecessor statements/owners unchanged;75 loaded candidate sources match successful compile hashes. NHC_DecodeModel.decoder_error and NKR_ScheduleExt.transition collector disagreements retained under(ab')(3)/(ax2); raw walks use only propext/Classical.choice/Quot.sound. Private rows_ext retained in raw inventory and successfully loaded by kernel name; combined source imports modules only.

NKR225 derives NKJ n+remaining<=4/canonical budgets at actual prefix2/prefix3/full4 arguments. Child233/234/260 and235 CLOSED in NLG are instantiated internally. NLN roots take only bf own-argument proof57607/Parsed-wire/root-binding/query-range domains; TX2<=12/9216gate and TX1<=10 derived internally. Exact Err(Parse)/Err(Merkle), both mutable arrays, ordered first-error histories and abort prefixes retained. NLE source extent/public/range work is SUPPORT ONLY on065/064; caller-native association remains OPEN.

Trust inventory: six NKR ReviewedTranscription entries and NKL-RT-batch_tree under existing option-A P6/D188 are reclassifications, never removals. No runtime/cryptographic trust-row changes. K086 liveness/abort; production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING. Pool397ON/278new/D30/6owners/3held inventory only; named producers/guards/sites OPEN, conditional read-to-settlement model retained. Poolb936275465/ELFe0e49c34…;121f3e29 historical. No verifier row depends on Pool ELF.

40/40 serial scopes,0Kani/0extraction; all admission exit0 AND allowed:true, hostfree>=40GB,6Ghigh/8Gmax/swap0/tasks64,Lean-M7000. Optional16G unused. Total wall{resources['wall_seconds']:.3f}s;peakRSS{resources['peak_rss_kib']}KiB;swaps0. Exact targets/commands/revisions/hashes/dependencies/metrics/axioms retained in NLO_ATTEMPTS.jsonl and per-scope receipts. No timeout,memory kill,unchanged rerun or cap increase. Own client repairs preserve validation; shared infrastructure untouched. Cache/TMPDIR retained.

Frozen verifier4bb3b3f5;frozen3;headline AspisR1.RPx_Deployed.deployed;L154 parameter;narrowedD188;100-bit PER-ATTEMPT/privacy/two-transaction contract unchanged. RuntimePersistence data-only;initial Pool seven fields only;RuntimeCpiReadonlyEntry7 unused;PDAop38 quantified,digest/error43/44. Entry/op9/native forest/Pool continuation,L187cold replay,L188artifact/extraction,NKT-F2/F3provenance remain. Focused coherent cached composition,not cold release replay. No shipped-source change or ELF rebuild trigger;pins inherited,not reproduced.
'''
(E/'NLO_PLAN_STATUS.md').write_text(plan);(E/'NLO_HANDOFF.md').write_text(plan.replace('status','handoff',1)+'\nRead NLO_LEDGER_DELTA.json,NLO_CANDIDATE_REVIEW.json,NLO_CLAUSE_MATRIX.json,NLO_PARENT_CLAUSES.json,NLO_AUDIT.json,NLO_SCAN.json,NLO_PHYSICAL.md,NLO_REMAINING.md. Seed NLO_EXPORT.json first,then NLO_PATHS.json. No push,sibling/session-A worktree edit,shipped-source/runtime trust change or key/account/fund/authority action.\n')
print(json.dumps(dict(status='PASS',closed=576,open=23,roots=len(results),modules=scan['modules'],scopes=40)))
