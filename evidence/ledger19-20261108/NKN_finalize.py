"""Admit exactly reviewed candidates after all combined gates; fail closed."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess
from NKN_report import report
E=Path(__file__).resolve().parent;P=E.parent/'ledger18-20261108'
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def raw(p):return p.read_bytes()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def put(n,x):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/n
 if n=='NKN_LEDGER.json'or len(b)>20_000_000:
  Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(b)
required=J(E/'NKN_AUDIT_ROOTS.json')['roots'];results=[];disagreements=[];nonzero=[]
for i in range(30):
 d=J(E/f'NKN_audit/batch{i}/proof{i}.json');results+=d['results']
 if d['exit_status']:nonzero.append(f'NKN_L{i+9:03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required)==len({r['root']for r in results})==10190
assert {r['root']for r in results}==set(required)
assert [r['root']for r in disagreements]==['NHC_DecodeModel.decoder_error']
fx=J(E/'NKN_audit/fixtures/fixtures.json');oldfx=J(P/'NKH_audit/fixtures/fixtures.json')
assert fx['exit_status']==0 and fx['results']==oldfx['results'] and len(fx['results'])==8
scan=[json.loads(l)for l in raw(E/'NKN_LOADED_scan.jsonl').decode().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
assert J(E/'NKN_audit/scan/scan.json')['exit_status']==0
put('NKN_SCAN.json',dict(exit_status=0,modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,canonical_duplicate_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan),scanner='NFX method; NKH_Driver module/path-only adaptation',attempt='NKN_L008',full_combined_import='NKN_COMBINED_IMPORT'))
rs=[json.loads(l)for l in(E/'NKN_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==len({r['attempt']for r in rs})==40
for r in rs:
 a=r['attempt'];rc=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'))
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0' and (r['exit_status']==0 or a in nonzero)
 disks=list(E.glob(a+'-disk*.json'));assert disks and any(J(p)['free']>=40_000_000_000 for p in disks)
resources=dict(scopes=40,complete_receipts=40,unused_scopes=0,kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),kani=0,extraction=0,aggregation16G_scopes=0,retained_nonzero_audit_exits=nonzero)
binary=J(E/'NKN_L006/NKN_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NKN_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
oldAudit=J(P/'NKH_AUDIT.json');canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean']);assert H(canonical)==oldAudit['walker']['sha256'];(E/'NKN_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NKN_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert raw(E/'NKN_L006/sources/NKN_native'/n)==raw(P/'NKH_L006/sources/NKH_native'/n)
assert J(E/'NKN_PREDECESSOR_COMPARISON.json')['status']=='PASS'
assert J(E/'NKN_NATIVE_REVIEW.json')['status']=='PASS_READ_ONLY_RECEIPT_REVALIDATION'
assert J(E/'NKN_SOURCE_REVIEW.json')['status']=='PASS'
assert J(E/'NKN_SOURCE_PINS.json')['status']=='PASS'
assert J(E/'NKN_OWNER_COMPARISON.json')['status']=='PASS'
assert J(E/'NKN_L039/receipt.json')['exit_status']==0 and J(E/'NKN_L040/receipt.json')['exit_status']==0
put('NKN_RESOURCES.json',resources)
put('NKN_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDING',full_composition_pass=True,combined='NKN_COMBINED_IMPORT',combined_attempt='NKN_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)",retained_nonzero_audit_exits=nonzero,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NKN_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NKN_WALKER_SOURCE.lean.txt',sha256=H(canonical),byte_identical=True,object_pins=actual,native_link_inputs_byte_identical_to_NKH=True),resources=resources,security_target_established=False,cold_release_replay=False))
basis=J(P/'NKH_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};review=J(E/'NKN_CANDIDATE_REVIEW.json');assert len(review['rows'])==11;changes=[]
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 o=copy.deepcopy(r['obligation']);o['NKN_basis_obligation']=copy.deepcopy(r['obligation']);o['certificate']=c['certificate'];o['kernel_roots']=c['kernel_statements'];o['NKN_complete_clause_review']=c['original_clauses'];o['NKN_hypothesis_inventory']=c['hypothesis_inventory'];o['NKN_root_domain']=c['root_domain'];o['NKN_semantic_review']=c['review'];o['NKN_baseline_amendment_review']=c['baseline_amendment_review']
 primary=next(k for k in c['kernel_statements']if k['root']==c['primary_root'])
 r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module=primary['owner_module'],owner_role='canonical checked row packet',root_owners=[dict(root=k['root'],owner_module=k['owner_module'],obligation_statement_sha256=H(k['obligation_statement'].encode()))for k in c['kernel_statements']],evidence_dir='evidence/ledger19-20261108')
 changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',primary_root=c['primary_root'],owner_module=r['owner_module'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],domain=c['root_domain'],roots=r['root_owners'],caller_clauses='All original clauses retained verbatim;26 additive own/unit clauses at parents in NKN_PARENT_CLAUSES.json.'))
parent=J(E/'NKN_PARENT_CLAUSES.json')
for rid in parent['parents']:
 r=by[rid];o=r['obligation'];o['NKN_parent_basis_obligation']=copy.deepcopy(oldby[rid]['obligation']);o['NKN_explicit_child_domains']=[c for c in parent['clauses']if c['parent']==rid];o['caller_domain_obligations'] += [c['caller_clause']for c in parent['clauses']if c['parent']==rid]
# Add actual prepared callee as an edge, not a fictitious row; preserve alternatives.
callee='crates/aspis-core/src/field.rs::PreparedQm31Multiplier::mul'
assert callee not in by['TX1:308']['canonical_callees']
by['TX1:308']['canonical_callees'].append(callee)
added_edge=dict(caller='TX1:308',callee=callee,new_row=False,status='DISCHARGED_RULE_A',emitted_law='AspisR1.FIv_PreparedTotal.mul',native_forwarding=['NKG_K044','NKG_K045','NKG_K046'],domain='PreparedFor SAME block selector and canonical SAME sum reply; NKG_AfterTotal.result / OracleChoices.ready derive it',original_edges_retained=True)
by['TX1:308']['obligation']['NKN_added_actual_callee']=added_edge
# Ruling(bb): preserve literal ten-leaf clause and mark supersession at TX2 calls.
literal='Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.'
replacement='TX2 queries[10..22]: at most12 distinct canonical indices<2^18 under9216-byte binary-entry gate, SAME produced idx/val/count/scratch, exact slot/node_count/padding and18 levels; ordered digest/error prefixes. NJV_TX2.TX2_093 imposes <=9216 bytes and native invocation only, no ten-leaf premise.'
reclass=dict(ruling='(bb)(3)',finding='NKB-F2',call_sites=['TX2:053','TX2:054','TX2:055'],original_literal=literal,literal_source='evidence/multiproof4-20261108/NJV_CALLER_CLAUSES.json:TX1:127.inventory (retained TX1 root also appears in TX2:093 certificate)',NKH_current_clause='Original binary-entry fixed-array ABI under <=9216 input bytes; generic entry law handles all counts/order by exact rejection. Ten-leaf unit and TX2 twelve-leaf caller clauses retained verbatim, no stronger hidden caller premise.',NKH_existing_U09_12_index_clauses_retained=True,status='SUPERSEDED_BY_FINDING',kept_never_deleted=True,replacement=replacement,producer='NKB_ProducerChain.verifier_bytes; caller must instantiate SAME produced scratch',child='TX2:093',child_credit_unchanged=True,child_root='NJV_TX2.TX2_093',credit_scope='TX2 <=12-index SAME-scratch caller instance under9216 bytes only; no new wider protocol credit',no_ten_leaf_root_hypothesis=True)
ledger.setdefault('inventory_clause_reclassifications',[]).append(reclass)
for rid in reclass['call_sites']:
 by[rid]['obligation']['NKN_bb3_superseded_unit']=copy.deepcopy(reclass)
 by[rid]['obligation']['caller_domain_obligations'].append(dict(id='NKN-bb3:'+rid,caller=by[rid]['function'],callee=by['TX2:093']['function'],required=replacement,status='OPEN',discharged_by=None,original_literal_kept=literal,ruling='(bb)(3)'))
finding=dict(id='NKB-F1',status='OPEN',rows=['TX1:083','TX2:055'],ruling='(bb)(1)-(2)',obligation='Frozen returns Err(Parse)/Err(Merkle); reused NJS_/Port3 pending-none terminal maps to fail. Exact returned Result native segment and same-prefix adopted fail transport, no suffix; parents propagate at SAME ? sites.',owner='NKL_ batch-merkle3')
ledger.setdefault('open_findings',[]).append(finding)
for rid in finding['rows']:by[rid]['obligation']['NKN_open_finding_NKB_F1']=copy.deepcopy(finding)
for r in ledger['rows']:
 old=oldby[r['row']];assert set(old['canonical_callees'])<=set(r['canonical_callees'])
 if r['obligation']!=old['obligation']:r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
for c in changes:c['complete_obligation_statement_hash']=by[c['row']]['obligation_statement_hash']
rt=[dict(item='NKJ-RT'+r,row='TX1:'+r,root=root,classification='ReviewedTranscription; P6/D188 option-A RECLASSIFICATION; never removal',scope='Actual frozen source segment/reference/native loop assembly, all Result arms on recorded canonical/arity/budget domains',provider_alias=next(f['trust']['reviewed_transcription']for f in J(E.parent/'field4-20261108/NKJ_CLOSED.json')['functions']if 'TX1:'+r in f['rows']))for r,root in [('036','NKJ_Root.accumulate'),('044','NKJ_Root.small'),('040','NKJ_Root.sum2'),('041','NKJ_Root.sum3'),('043','NKJ_Root.sum4')]]
ledger['reviewed_transcription_inventory']+=rt
assert ledger['trust_rows']==basis['trust_rows']
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':553,'OPEN':46}
assert {r['row']for r in ledger['rows']if r['status']!=oldby[r['row']]['status']}=={c['row']for c in changes}
ledger.update(basis='NKH ledger18 plus11 NKN-gated NKA/NKG/NKJ candidates; original edges and clauses retained',basis_delta='NKN_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NKN_LEDGER.json',ledger)
put('NKN_LEDGER_DELTA.json',dict(basis='evidence/ledger18-20261108/NKH_LEDGER.json.xz',before=dict(CLOSED=542,QUALIFIED=0,OPEN=57),after=dict(CLOSED=553,QUALIFIED=0,OPEN=46),new_closed_rows=[c['row']for c in changes],new_count=11,rows=changes,no_double_count=True,no_other_status_change=True,explicit_parent_clause_updates=parent,added_edges=[added_edge],inventory_clause_reclassifications=[reclass],open_findings=[finding],reviewed_transcription_additions=rt,trust_rows_changed=False,security_target_established=False,rejected_candidates=[],supporting_only=['NKB_ batch-merkle2','NKF_ tx2-adapters'],gate=[r['attempt']for r in rs]))
put('NKN_TRUST_INVENTORY.json',dict(runtime_cryptographic_rows_unchanged=True,runtime_rows_sha256=H(json.dumps(basis['trust_rows'],sort_keys=True).encode()),added_reviewed_transcription_items=rt,removed=[],classification='Option-A P6/D188 RECLASSIFICATION, never removal',op38='quantified; no PDA value row',digest_error_slots=[43,44],RuntimePersistence='data-only',RuntimeCpiReadonlyEntry7='unused'))
review['status']='PASS_COMPLETE_OBLIGATIONS_CANONICAL_OWNERS_AND_FULL_GATE';review['gate_pass']=True
for c in review['rows']:c['gate_admitted']=True
put('NKN_CANDIDATE_REVIEW.json',review)
report(ledger,resources)
plan=f'''# NKN plan status\n\nTarget not yet established. Twelfth all-slices composition gate PASS:553 CLOSED /0 QUALIFIED /46 OPEN of599, against NKH542/0/57. Exactly11 occurrences admitted: NKA2, NKG4, NKJ5. No other promotion. All original edges and clauses retained;26 additive own-domain/unit clauses recorded at parents. No unsubmitted parent receives credit.\n\nAll10190 roots raw-audited over this job's combined import, standard axioms only. Same optimized binary/eight fixtures PASS; NFX exit0 across{len(scan)}modules, zero dangling/canonical duplicate/incompatible owners/import defects; compatible theorem-cache replicas disclosed. NHC_DecodeModel.decoder_error raw/collector disagreement and actual nonzero audit exit retained under(ab')(3). All10066 NKH statements/owners unchanged; full selected closure pins and inherited Aeneas objects retained.\n\nNKA129 universal Reservation, both allocator arms, SAME1392/align4 owned carrier/init/cleanup. NKA069 SAME066/067 arguments, domains internally derived; spurious edge202 retained under(az)(1). NKG308 deterministic, no security-oracle premise; added PreparedQm31Multiplier::mul edge uses only PreparedFor/canonical rule-A law, no new row. NKJ actual frozen segments cover all Result arms/full records; five shape-fidelity families reviewed, K003/K004 to Kissat K005/K006 changed backend under(ba), no cap increase or Kani field multiplication. Root domains, including n+remaining<=4, remain caller-owned at225.\n\n(ba)/(bb) recorded. Literal TX2 ten-leaf unit retained SUPERSEDED_BY_FINDING; replaced there by <=12 canonical indices/9216-byte entry and SAME scratch. NJV_TX2.TX2_093 credit is consumed only at that12-index/9216-byte caller instance; its stronger rejection theorem needs no ten-leaf premise. NKB-F1 Err(Parse)/Err(Merkle) vs pending-none terminal remains OPEN on083/055; NKL owns remedy.\n\nOnly new trust inventory entries: ReviewedTranscription NKJ-RT036/044/040/041/043, option-A RECLASSIFICATION, never removal. Runtime/cryptographic rows unchanged. K086 remains liveness/abort finding; production reachability/exclusion UNPROVED. Owner decision(aj)(a) PENDING. Frozen3/deployed headline/L154 statement parameter/narrowedD188/100-bit PER-ATTEMPT/privacy/two transactions unchanged. RuntimePersistence data-only, initial Pool seven fields, RuntimeCpiReadonlyEntry7 unused; op38 quantified, digest/error43/44. All named Pool production obligations remain OPEN/conditional as named.\n\n40/40 serial scopes,0Kani/0extraction; all admission exit0 AND allowed:true,6Ghigh/8Gmax/swap0/tasks64,-M7000. Optional16G unused. Total scope wall{resources['wall_seconds']:.3f}s, peakRSS{resources['peak_rss_kib']}KiB,swaps0. Per-scope exact targets/exit/wall/RSS/swap/revisions/axioms/source/dependency pins retained. No shipped-source change or ELF rebuild trigger; artifact hashes inherited only. Entry/op9/native parent/Pool continuation,L187cold replay,L188artifact/extraction remain.\n'''
(E/'NKN_PLAN_STATUS.md').write_text(plan)
(E/'NKN_HANDOFF.md').write_text(plan.replace('# NKN plan status','# NKN ledger19 handoff')+'\nRead NKN_LEDGER_DELTA.json, NKN_CANDIDATE_REVIEW.json, NKN_PARENT_CLAUSES.json, NKN_AUDIT.json, NKN_SCAN.json, NKN_PHYSICAL.md and NKN_REMAINING.md. Export NKN_EXPORT.json; prepend its retained export to NKN_PATHS.json. This is a coherent focused composition, not a cold release rebuild. No push, sibling/session-A edits, wallet/key/fund/authority action or runtime trust change.\n')
print(json.dumps(dict(status='PASS',closed=553,open=46,roots=len(required),modules=len(scan),scopes=40)))
