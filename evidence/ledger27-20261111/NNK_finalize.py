"""Promote only after the complete combined/raw/NFX/retention gate."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'ledger26-20261111';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.is_file():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):return json.loads(lzma.decompress(raw(p))if p.suffix=='.xz'else raw(p))
def put(n,x,compress=False):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/('NNK_'+n+'.json')
 if compress or len(b)>20_000_000:Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
assert J(E/'NNK_audit/verify/NNK_GATE_INTEGRITY.json')['status']=='PASS'
required=J(E/'NNK_AUDIT_ROOTS.json');results=[];disagreements=[]
for i,group in enumerate(required['groups']):
 d=J(E/'NNK_audit'/('batch'+str(i))/('proof'+str(i)+'.json'));assert [r['root']for r in d['results']]==group,(i,len(d['results']),len(group))
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r
  if not r['equal']:
   assert r['root']in {'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition','LIB_VCarriers.Acc'},r
   disagreements.append(r)
 results+=d['results']
assert len(results)==len({r['root']for r in results})==len(required['roots']);assert set(r['root']for r in results)==set(required['roots'])
fixtures=J(E/'NNK_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and len(fixtures['results'])==8 and fixtures['results']==J(P/'NNI_audit/fixtures/fixtures.json')['results']
scan=J(E/'NNK_audit/scan/scan.json');assert scan['exit_status']==0
loaded=[json.loads(l)for l in raw(E/'NNK_LOADED_scan.jsonl').decode().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
put('SCAN',dict(status='PASS',exit_status=0,combined='NNK_COMBINED_IMPORT',modules=len(loaded),dangling=0,canonical_duplicate_owners=0,import_mismatches=0,cached_replicas=sum(len(r['cached_replicas'])for r in loaded)))
statements={}
for l in raw(E/'NNK_L056/stdout.log').decode().splitlines():
 if 'NNK_OWNER 'in l:
  r=json.loads(l.split('NNK_OWNER ',1)[1]);assert r['root']not in statements;statements[r['root']]=r
assert set(statements)==set(required['roots'])
prior=J(P/'NNI_KERNEL_STATEMENTS.json.xz');wrong=[n for n,r in prior.items()if statements.get(n)!=r];assert not wrong,wrong[:5]
put('KERNEL_STATEMENTS',statements,True);put('OWNER_COMPARISON',dict(status='PASS',previous=len(prior),identical=len(prior),new=len(statements)-len(prior),wrong=[]))
entries=[json.loads(l)for l in(E/'NNK_ATTEMPTS.jsonl').read_text().splitlines()];receipts=[r for r in entries if 'exit_status'in r];assert len(receipts)==len({r['attempt']for r in receipts})<=60
for row in receipts:
 a=row['attempt'];r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'))
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0';assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
 checks=[c for c in entries if c.get('attempt')==a and c.get('event')=='share_check'];assert checks and checks[-1]['host']['count']<6
 if r['exit_status']:assert r['kind']=='audit'and r['module'].startswith('batch'),(a,r['exit_status'])
resources=dict(scopes=len(receipts),budget=60,unused=60-len(receipts),kinds=dict(collections.Counter(r['kind']for r in receipts)),wall_seconds=sum(r['wall_seconds']for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=sum(int(r['swaps'])for r in receipts),kani=0,extraction=0,aggregation16G_scopes=0,one_scope_at_a_time=True,retained_collector_exit_attempts=[r['attempt']for r in receipts if r['exit_status']],timeout_or_memory_kill=[])
binary=J(E/'NNK_L001/NNK_ProofDriver_BINARY_PIN.json')['sha256'];assert binary==J(P/'NNI_AUDIT.json')['same_optimized_proof_binary_sha256']
assert J(E/'NNK_PREDECESSOR_COMPARISON.json')['status']=='PASS'and J(E/'NNK_FINAL_HOST.json')['status']=='PASS'
put('RESOURCES',resources);put('AUDIT',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_COLLECTOR_FINDINGS',full_composition_pass=True,combined='NNK_COMBINED_IMPORT',combined_attempt='NNK_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(results),new_roots=len(statements)-len(prior),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)/(ax2)",same_optimized_proof_binary_sha256=binary,fixtures=fixtures['results'],scanner='NNK_SCAN.json',walker=J(P/'NNI_AUDIT.json')['walker'],resources=resources,cold_release_replay=False,security_target_established=False))
basis=J(P/'NNI_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};review=J(E/'NNK_CANDIDATE_REVIEW.json');clauses=J(E/'NNK_CLAUSE_REVIEW.json');newrows=[]
for c in review['candidates']:
 assert c['status']=='STATIC_REVIEW_PASS_GATE_PENDING';name=c['candidate'];r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 assert statements[name]['owner_module']==c['owner'];c.update(status='PASS_COMPLETE_ROOT_GATE_ADMITTED',gate_admitted=True,kernel_statement=statements[name])
 for child in c['canonical_children']:
  assert by[child['row']]['status']=='CLOSED',(r['row'],child['row']);child['status']='CLOSED';child['roots']=by[child['row']]['root_owners']
 old=copy.deepcopy(r['obligation']);o=r['obligation'];o['NNK_basis_obligation']=old;o['NNK_complete_candidate_review']=c;o['NNK_root_domain']=c['own_input_clauses'];o['kernel_roots']=[statements[name]]
 o['NNK_complete_clause_review']=[z for z in clauses['original_clauses']if z['row']==c['row']]
 for kind in ['caller_domain_obligations','inventory_domain_obligations']:
  for z in o[kind]:z.update(status='INTERNAL_DISCHARGED_WITH_OWN_INPUT_PROVENANCE_RETAINED',discharged_by=name,NNK_evidence=c.get('source_chain',c.get('reference_roots')),NNK_note='Full canonical RowSpec fold at same entered arguments; original own-input clauses remain upstream. Historical provenance-support clauses retain source meaning; no new child edge or stronger input premise.')
 o['certificate'].update(bridge_status='CLOSED',composed_status='CLOSED',NNK_root=name,NNK_gate='PASS',NNK_route=c.get('source_route','(ah) reviewed reference / actual native segment contracts and Lean induction; ruling(br)'),no_credit_reason='Historical rejection retained in NNK_basis_obligation, superseded for this row by complete NNK gate')
 trust=set(r.get('consumes_trust',[]))|{'NativeContractSemanticTransport','TrustedStd','AllocatorABICompilerSourceToELF'}
 if r['row']=='TX2:217':trust.add('ReviewedTranscription-TX2:217')
 r.update(previous_status='OPEN',status='CLOSED',owner_module=c['owner'],owner_role='canonical complete revision3 source/observation root',root_owners=[dict(root=name,owner_module=c['owner'],obligation_statement_sha256=H(statements[name]['obligation_statement'].encode()))],evidence_dir='evidence/ledger27-20261111',consumes_trust=sorted(trust),consumes_trust_inherited_children=[dict(row=z['row'],roots=z['roots'],retained_row_consumes_trust=by[z['row']].get('consumes_trust',[]),certificate_trust=by[z['row']]['obligation']['certificate'].get('trust'))for z in c['canonical_children']])
 newrows.append(r['row'])
 # Record increased extraction reliance, never remove the prior item or claim fresh entire-closure provenance.
 if r['row']!='TX2:217':ledger['extraction_trust_reclassifications'].append(dict(item='NNK-'+r['row']+'-emitted-body-bm',row=r['row'],root=name,classification='RECLASSIFICATION: existing extraction item narrowed by(bc); increased reliance under(bm); no new cryptographic trust and nothing removed',fresh_parent_provenance=True,emission='NMP_E002'if r['row'].startswith('TX1')else'NMX_E005 LLBC / E006 Aeneas',child_provenance='(bk) unresolved inherited provenance retained',source_to_ELF='not newly established'))
# Explicit own-input caller clauses stay visible at parent094.
parent=by['TX1:094'];parent['obligation']['NNK_087_own_inputs']=J(E/'NNK_PARENT_CLAUSES.json')['TX1:087']
if not any(z.get('id')=='RSL3-caller:TX1:094:TX1:087:R4'for z in parent['obligation']['caller_domain_obligations']):parent['obligation']['caller_domain_obligations'].append(dict(id='RSL3-caller:TX1:094:TX1:087:R4',callee=by['TX1:087']['function'],status='OPEN',discharged_by=None,required='LIB_Instances.VL.checkValuesDom (slice SAME original proof OFF_Y1 OFF_INACTIVE)',proof_support='canonical_scan SAME-proof R4 support in NNG_; not full094 candidate',finding='NNG_FINDING094 installed parseShape domain mismatch; do not narrow Domain094'))
# Mark internally supplied137 input clauses without claiming the still-open094 caller.
by['TX1:087']['obligation']['NNK_137_input_discharge']=J(E/'NNK_PARENT_CLAUSES.json')['TX1:137']
for row in ['TX1:137','TX1:087']:
 by[row]['obligation']['NNK_literal_domain_is_only_input']=True
for t in ledger['trust_rows']:
 if t['id']=='ReviewedTranscription-TX2:217':t['NNK_consumer_addition']='TX2:217 NMX_R3_DecoderFold.root, gate admitted under(br)';t['consumed_by_closed_rows']=sorted(set(t.get('consumed_by_closed_rows',[]))|{'TX2:217'});t['direct_closed_rows']=['TX2:217']
 if t['id']in ['ReviewedTranscription-TX1:344','ReviewedTranscription-TX2:240']:assert not t.get('consumed_by_closed_rows')
for t in ledger['reviewed_transcription_inventory']:
 if t['id']=='ReviewedTranscription-TX2:217':t['NNK_consumer_addition']='TX2:217 gate admitted under(br)';t['consumed_by_closed_rows']=['TX2:217'];t['direct_closed_rows']=['TX2:217']
ledger['NNK_top_composition']=J(E/'NNK_TOP_COMPOSITION.json');ledger['NNK_specification']=J(E/'NNK_SPECIFICATION.json');ledger['NNK_K086']=J(E/'NNK_K086.json');prov=J(E/'NNK_PROVENANCE.json');assert prov['gate_reachability_used'];ledger['NNK_extraction_provenance']=prov
for r in ledger['rows']:
 assert r['canonical_callees']==oldby[r['row']]['canonical_callees']
 if r['obligation']!=oldby[r['row']]['obligation']:r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
assert set(newrows)=={'TX1:137','TX1:087','TX2:217','TX2:234'};assert by['TX2:233']['status']=='OPEN'
assert {r['row']for r in ledger['rows']if r['status']!=oldby[r['row']]['status']}==set(newrows)
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':587,'OPEN':12}
ledger.update(basis='ledger26 NNI_LEDGER plus four NNK-gated roots;599 rows/every edge retained',basis_delta='NNK_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('LEDGER',ledger,True);put('LEDGER_DELTA',dict(basis='evidence/ledger26-20261111/NNI_LEDGER.json.xz',basis_uncompressed_sha256=(P/'NNI_LEDGER.json.sha256').read_text().strip(),before=dict(CLOSED=583,QUALIFIED=0,OPEN=16),after=dict(CLOSED=587,QUALIFIED=0,OPEN=12),new_closed_rows=newrows,new_count=4,rows=[dict(row=c['row'],root=c['candidate'],previous_status='OPEN',status='CLOSED',own_input_clauses=c['own_input_clauses'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],complete_obligation_statement_hash=by[c['row']]['obligation_statement_hash'])for c in review['candidates']],added_edges=[],removed_edges=[],trust_inventory_additions=[],trust_inventory_removals=[],trust_consumer_additions=['ReviewedTranscription-TX2:217'],wrapper_trust_unused=['ReviewedTranscription-TX1:344','ReviewedTranscription-TX2:240'],extraction_trust_reclassifications=[x for x in ledger['extraction_trust_reclassifications']if x.get('item','').startswith('NNK-')],top_composition_not_row_counts=True,provenance_conservative_impact=len(prov['current_conservative_affected_CLOSED_rows']),pool_promotions=[],security_target_established=False))
review.update(gate='PASS');put('CANDIDATE_REVIEW',review)
for c in clauses['original_clauses']:c['status']='DISCHARGED_IN_COMPLETE_SOURCE_FOLD';c['NNK_gate_credit']='Complete combined/raw/NFX gate PASS; original own-input clauses remain upstream'
put('CLAUSE_REVIEW',clauses)
print(json.dumps(dict(gate='PASS',counts=counts,resources=resources,provenance=len(prov['current_conservative_affected_CLOSED_rows']))))
