"""Admit exactly five rows only after the complete current-context gate."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess
E=Path(__file__).resolve().parent;R=E.parent;P=R/'ledger29-20261111';H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.open(p).read()if str(p).endswith('.xz')else p.read_text())
def put(n,x,compressed=False):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/('NNN_'+n+'.json')
 if compressed or len(b)>20_000_000:Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
basis=J(P/'NNM_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};old={r['row']:r for r in basis['rows']}
receipts=[J(p)for p in sorted(E.glob('NNN_L*/receipt.json'))];assert len(receipts)<=40
entries=list(map(json.loads,(E/'NNN_ATTEMPTS.jsonl').read_text().splitlines()))
for rc in receipts:
 a=rc['attempt'];ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'};assert str(rc['swaps'])=='0'
 assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
 checks=[z for z in entries if z.get('attempt')==a and z.get('event')=='share_check'];assert checks and checks[-1]['host']['count']<6
 if rc['exit_status']:assert a=='NNN_L004'and rc['exit_status']==1
 assert rc['source_revision'] and rc['source_hashes'] and 'selected_objects'in rc['deps_fingerprint']
scan=list(map(json.loads,(E/'NNN_LOADED_scan.jsonl').read_text().splitlines()));assert J(E/'NNN_L009/receipt.json')['exit_status']==0
assert all(not x['dangling']and not x['duplicate_owners']and x['imports_match']for x in scan)
assert H((E/'NNN_EXPECTED_IMPORTS.jsonl').read_bytes())==J(E/'NNN_L009/receipt.json')['source_hashes']['NNN_EXPECTED_IMPORTS.jsonl']
assert H((E/'NNN_COMBINED_IMPORT.lean').read_bytes())==J(E/'NNN_L006/receipt.json')['source_hashes']['NNN_sources/NNN_COMBINED_IMPORT.lean']
for m in ['NMV_RslDomain','NMV_RslFold','NMV_RslLaws','NMV_RslSnapshots']:assert sum(x['module']==m for x in scan)==1
pins=J(E/'NNN_CLOSURE_PINS.json.xz');assert pins['status']=='PASS'and pins['predecessor_modules_unchanged']==19189 and pins['predecessor_companions_unchanged']==16593
assert J(E/'NNN_SOURCE_REVIEW.json')['status']=='PASS';assert J(E/'NNN_FROZEN_SOURCE_CHECK.json')['status']=='PASS'
raw=[]
for l in (E/'NNN_L008/stdout.log').read_text().splitlines():
 if l.startswith('NEP_RESULT '):raw.append(json.loads(l[11:]))
assert len(raw)==4 and J(E/'NNN_L008/receipt.json')['exit_status']==0
assert all(z['equal']and set(z['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for z in raw)
prior=J(P/'NNM_AUDIT.json');assert prior['full_composition_pass']and prior['raw_standard_axioms_only']
fin=J(R/'fin-host-20261108/NNO_audit/final/proof0.json');assert fin['exit_status']==0 and len(fin['results'])==5
assert all(z['equal']and set(z['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for z in fin['results'])
review=J(E/'NNN_CANDIDATE_REVIEW.json');clauses=J(E/'NNN_CLAUSE_REVIEW.json');parent=J(E/'NNN_PARENT_CLAUSES.json');statements=J(E/'NNN_KERNEL_STATEMENTS.json')
newrows=[]
base_trust={'NativeContractSemanticTransport','TrustedStd','AllocatorABICompilerSourceToELF'}
window_trust={'S2TrustedSdkBorrow','RuntimeClockSlotBinding','RuntimeReturnDataClear','ReviewedTranscription-TX2:240'}
clause_by={(z['row'],z['kind']):[]for z in clauses['clauses']}
for z in clauses['clauses']:clause_by[(z['row'],z['kind'])].append(z)
for c in review['candidates']:
 r=by[c['row']];name=c['theorem'];assert r['status']=='OPEN'
 for child in c['canonical_children']:
  z=by[child['row']];assert z['status']=='CLOSED',(r['row'],child['row']);child.update(status='CLOSED',roots=z['root_owners'])
 prior_o=copy.deepcopy(r['obligation']);o=r['obligation'];o['NNN_basis_obligation']=prior_o;o['NNN_complete_candidate_review']=c;o['kernel_roots']=[statements[name]];o['named_hypotheses']=[]
 for kind in ['caller_domain_obligations','inventory_domain_obligations']:
  for z in o[kind]:
   matches=[d for d in clause_by[(r['row'],kind)]if d['original']==z];assert len(matches)==1
   d=matches[0];z.update(status=d['status'],discharged_by=d['discharged_by'],NNN_evidence=d['reason'])
 o['NNN_own_input_clauses']=[z for z in parent['clauses']if r['row']in z.get('rows',[z.get('row',z.get('caller'))])]
 o['certificate'].update(bridge_status='CLOSED',composed_status='CLOSED',NNN_root=name,NNN_gate='PASS',NNN_route='(bn) reviewed source-fission wrapper'if r['row']=='TX2:240'else'(bm) frozen emitted-body fold with CLOSED same-input children',no_credit_reason='Historical reasons retained in NNN_basis_obligation, superseded by exact instantiated FIN root gate')
 trust=set(base_trust)
 if r['row']=='TX2:240':trust|=window_trust
 for child in c['canonical_children']:trust.update(by[child['row']].get('consumes_trust',[]))
 c.update(gate_admitted=True,gate_status='PASS_COMPLETE_ROOT_GATE_ADMITTED',status='CLOSED',consumes_trust=sorted(trust))
 r.update(previous_status='OPEN',status='CLOSED',owner_module=statements[name]['owner_module'],owner_role='canonical complete revision4 instantiated source/observation root',root_owners=[dict(root=name,owner_module=statements[name]['owner_module'],obligation_statement_sha256=H(statements[name]['obligation_statement'].encode()))],evidence_dir='evidence/ledger30-20261111',consumes_trust=sorted(trust),consumes_trust_inherited_children=[dict(row=z['row'],roots=by[z['row']]['root_owners'],retained_row_consumes_trust=by[z['row']].get('consumes_trust',[]))for z in c['canonical_children']])
 r['obligation_statement_hash']=H(json.dumps(o,sort_keys=True,separators=(',',':')).encode());newrows.append(r['row'])
 if r['row']!='TX2:240':ledger['extraction_trust_reclassifications'].append(dict(item='NNN-'+r['row']+'-emitted-body-bm',row=r['row'],root=name,classification='RECLASSIFICATION of existing extraction item narrowed by(bc); increased reliance under(bm), never removal',fresh_parent_provenance=True,emission='NMW_E002 (process)'if r['row']in ['TX1:333','TX2:221']else'NMW_E001 (entry)',attempt_labels='Actual receipts correct task label reversal',child_provenance='(bk) unresolved inherited provenance retained',source_to_ELF='not newly established'))
assert newrows==['TX2:240','TX1:333','TX2:221','TX1:330','TX2:213']
# Reconcile the stale row-level finding, retaining all historical wording.
for z in ledger['open_findings']:
 if z['id']=='NKB-F1':z.update(status='RESOLVED',resolution='NKL-RT-batch_tree composed by NLN_TX1_083.root / NLN_TX2_055.root, both CLOSED in ledger22 and unchanged; exact returned errors and same-prefix fail transport retained',resolved_roots=by['TX1:083']['root_owners']+by['TX2:055']['root_owners'],previous_status='OPEN')
 elif z['id']=='NKT-F2':z['NNN_scope']='Extraction provenance finding retained as release/top reporting; not a contradictory row-domain finding. No row reopened under(bk)/(bt).'
 elif z['id']=='NKT-F3':z['NNN_scope']='Inherited zero-root accessor-packet inventory finding retained explicitly; those two historical CLOSED rows are not newly credited or claimed to have new native evidence. No row promotion here depends on inventing a root.'
# Update use, never the trust statements or removal conditions.
for tr in ledger['trust_rows']:
 consumers={n for n in newrows if tr['id']in by[n]['consumes_trust']};tr['consumed_by_closed_rows']=sorted(set(tr.get('consumed_by_closed_rows',[]))|consumers)
 if tr['id']=='ReviewedTranscription-TX2:240':tr.update(status='USED',NNN_consumer='FIN_240.candidate',NNN_status='USED',direct_closed_rows=['TX2:240'],transitive_consumers=['FIN_333.candidate','FIN_221.candidate','FIN_330.candidate','FIN_213.candidate'],NNN_TGB4='RuntimeClockSlotBinding deployed owned.rs:479 and Err arm reporting correction included; no RowSpec change')
 if tr['id']=='ReviewedTranscription-TX1:344':tr['transitive_consumers']=sorted(set(tr.get('transitive_consumers',[]))|{'FIN_333.candidate','FIN_221.candidate','FIN_330.candidate','FIN_213.candidate'})
for tr in ledger['reviewed_transcription_inventory']:
 if tr.get('item',tr.get('id'))in ['ReviewedTranscription-TX1:344','ReviewedTranscription-TX2:240']:
  tr.update(NNN_status='USED',NNN_consumer='FIN_240.candidate'if tr.get('item',tr.get('id'))=='ReviewedTranscription-TX2:240'else'AspisR1.NNG_Candidate344.candidate',transitive_consumers=['FIN_333.candidate','FIN_221.candidate','FIN_330.candidate','FIN_213.candidate'])
top=J(E/'NNN_TOP_COMPOSITION.json')
for z in top['top_composition_obligations']:
 if z['id']=='TOP:G1b':z['canonical_row_disposition']='CLOSED canonical240/221/213 and paired TX1 rows; weak/library-parametric241 remains OPEN'
ledger['top_composition_obligations']=top['top_composition_obligations'];ledger['NNN_top_composition']=top;ledger['NNN_extraction_provenance']=J(E/'NNN_PROVENANCE.json');ledger['NNN_specification']=copy.deepcopy(basis['NNM_specification']);ledger['NNN_K086']=copy.deepcopy(basis['NNM_K086']);ledger['NNN_headline_inventory']=parent['entry_headline_inventory']
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':599};assert all(by[n]==old[n]for n in by if n not in newrows)
for n in by:assert by[n]['canonical_callees']==old[n]['canonical_callees']
ledger.update(basis='ledger29 NNM_LEDGER plus five NNN-gated FIN instantiations; every edge retained',basis_delta='NNN_LEDGER_DELTA.json',counts={'CLOSED':599,'QUALIFIED':0,'OPEN':0},gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('LEDGER',ledger,True);review['gate']='PASS';put('CANDIDATE_REVIEW',review);put('TOP_COMPOSITION',top);clauses.update(gate='PASS',current_note='Canonical five FIN roots gated; own-input Root0/entry clauses remain carried explicitly to headline, ledger29 records retained verbatim');put('CLAUSE_REVIEW',clauses)
put('LEDGER_DELTA',dict(basis='evidence/ledger29-20261111/NNM_LEDGER.json.xz',basis_uncompressed_sha256=(P/'NNM_LEDGER.json.sha256').read_text().strip(),before={'CLOSED':594,'QUALIFIED':0,'OPEN':5},after=ledger['counts'],new_closed_rows=newrows,new_count=5,rows=[dict(row=n,root=by[n]['root_owners'][0]['root'],previous_status='OPEN',status='CLOSED',own_input_clauses=by[n]['obligation']['NNN_own_input_clauses'],basis_obligation_statement_hash=old[n]['obligation_statement_hash'],complete_obligation_statement_hash=by[n]['obligation_statement_hash'])for n in newrows],added_edges=[],removed_edges=[],trust_inventory_additions=[],trust_inventory_removals=[],wrapper_trust_used=['ReviewedTranscription-TX1:344','ReviewedTranscription-TX2:240'],provenance_conservative_impact=578,no_top_obligation_affects_row_counts=True,security_target_established=False))
put('SCAN',dict(status='PASS',exit_status=0,attempt='NNN_L009',combined='NNN_COMBINED_IMPORT',modules=len(scan),declarations=sum(x['declarations']for x in scan),dangling=0,canonical_duplicate_owners=0,import_mismatches=0,cached_replicas=sum(len(x['cached_replicas'])for x in scan),identical_serialized_replicas=sum(z['proof_identical']for x in scan for z in x['cached_replicas']),theorem_cache_proof_variants=[z for x in scan for z in x['cached_replicas']if not z['proof_identical']],replica_evidence='NNN_LOADED_scan.jsonl; proof variants have structurally identical theorem types/levels/mutual metadata, classified by the unchanged inherited NFX proof-irrelevance method',canonical_NMV_owners={m:m for m in ['NMV_RslDomain','NMV_RslFold','NMV_RslLaws','NMV_RslSnapshots']},failed_preflight='NNN_L004 own expected-import omissions; source-derived repair, unchanged scan driver'))
resources=dict(scopes=len(receipts),budget=40,unused=40-len(receipts),Kani=0,extraction=0,one_scope_at_a_time=True,aggregation16G_scopes=0,wall_seconds=sum(r['wall_seconds']for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=sum(int(r['swaps'])for r in receipts),timeout_or_memory_kill=[],failed_attempts=[dict(attempt=r['attempt'],exit=r['exit_status'],reason='own expected-import inventory missing34 supplemental sources')for r in receipts if r['exit_status']],unused_budget_reason='Every one of five assigned row members and the required composition gate completed. TOP weak241/NMF_B/G0/O2 are outside ledger30 ownership; no remaining assigned member can be attempted. No repeated unchanged passing audit is authorized.')
put('RESOURCES',resources)
put('PREDECESSOR_COMPARISON',dict(status='PASS',rows_unchanged=594,root_statements_and_owners_unchanged=prior['required_roots'],selected_modules_unchanged=pins['predecessor_modules_unchanged'],companion_objects_unchanged=pins['predecessor_companions_unchanged'],method='Every predecessor selected olean AND companion hash unchanged. Same kernel types/owners and existing raw walks reused; no re-audit of unchanged objects.',NNO_candidates='all5 source/own object hashes unchanged, exact statement rfl checks and raw walks reused',NNP='LIBW/NNP exported objects unchanged;19 LIBW roots and25 new support roots reuse passing raw audits, combined closure checked by current scan'))
put('AUDIT',dict(status='PASS',full_composition_pass=True,combined='NNN_COMBINED_IMPORT',combined_attempt='NNN_L006',statement_attempt='NNN_L007',scanner='NNN_SCAN.json',new_raw_attempt='NNN_L008',new_roots=raw,reused_FIN_raw=fin,reused_ledger29_required_roots=prior['required_roots'],reused_LIBW_raw='NNP_FINAL_proof0/1,44 roots standard-only',reused_eight_fixtures='NNO_audit/final/fixtures.json unchanged walker, no repetition',raw_standard_axioms_only=True,raw_authoritative_ruling="(ab')(3)/(ax2)",inherited_collector_findings=prior['collect_axioms_disagreements'],same_optimized_proof_binary_sha256='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c',resources=resources,cold_release_replay=False,security_target_established=False))
print(json.dumps(dict(gate='PASS',counts=ledger['counts'],resources=resources)))
