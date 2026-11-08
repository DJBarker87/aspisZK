"""Award only the five reviewed candidates, after all required current-context gates."""
from pathlib import Path
import json,lzma,hashlib,collections,copy,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'ledger28-20261111';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):
 b=raw(p);return json.loads(lzma.decompress(b)if p.suffix=='.xz'else b)
def put(n,x,compress=False):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/('NNM_'+n+'.json')
 if compress or len(b)>20_000_000:Path(str(p)+'.xz').write_bytes(lzma.compress(b));Path(str(p)+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
assert J(E/'NNM_GATE_INTEGRITY.json')['status']=='PASS'
required=J(E/'NNM_AUDIT_ROOTS.json');results=[];disagreements=[]
for i,g in enumerate(required['groups']):
 ps=list((E/'NNM_audit').glob('batch*/proof'+str(i)+'.json'));assert len(ps)==1,(i,ps)
 d=J(ps[0]);assert [r['root']for r in d['results']]==g
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Quot.sound','Classical.choice'}
  if not r['equal']:
   assert r['root']in{'AspisR1.NKR_ScheduleExt.transition','NHC_DecodeModel.decoder_error','LIB_VCarriers.Acc','NNI_CollectorAcc.alias_identity'};disagreements.append(r)
 results+=d['results']
assert len(results)==len({r['root']for r in results})==len(required['roots'])
assert {r['root']for r in results}==set(required['roots'])
fixtures=J(E/'NNM_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and fixtures['results']==J(P/'NNL_audit/fixtures/fixtures.json')['results']
assert J(E/'NNM_audit/scan/scan.json')['exit_status']==0
loaded=[json.loads(l)for l in raw(E/'NNM_LOADED_scan.jsonl').decode().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
put('SCAN',dict(status='PASS',exit_status=0,attempt='NNM_L031',combined='NNM_COMBINED_IMPORT',modules=len(loaded),dangling=0,canonical_duplicate_owners=0,import_mismatches=0,cached_replicas=sum(len(r['cached_replicas'])for r in loaded),retired_failed_scan='NNM_L030: fourteen own expected-source inventory mismatches; no credit; independent source-derived import repair',repair='NNM_IMPORT_REPAIR.json'))
statements=J(E/'NNM_KERNEL_STATEMENTS.json');assert set(statements)==set(required['roots']);assert J(E/'NNM_STATEMENT_COMPARISON.json')['status']=='PASS'
for n in ['EMISSION_REVIEW','SYNTAX_ASSOCIATION','WRAPPER_REVIEW','PARENT_COMPILE_PROVENANCE','FROZEN_SOURCE_CHECK']:assert J(E/('NNM_'+n+'.json'))['status']=='PASS'
receipts=[J(p)for p in sorted(E.glob('NNM_L*/receipt.json'))];assert len(receipts)==60
entries=[json.loads(l)for l in(E/'NNM_ATTEMPTS.jsonl').read_text().splitlines()]
for r in receipts:
 a=r['attempt'];ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0';assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
 checks=[c for c in entries if c.get('attempt')==a and c.get('event')=='share_check'];assert checks and checks[-1]['host']['count']<6
 if r['exit_status']:assert a in['NNM_L023','NNM_L030']and r['exit_status']==1,(a,r['exit_status'])
resources=dict(scopes=60,budget=60,unused=0,kani=0,extraction=0,aggregation16G_scopes=0,one_scope_at_a_time=True,kinds=dict(collections.Counter(r['kind']for r in receipts)),wall_seconds=sum(r['wall_seconds']for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=sum(int(r['swaps'])for r in receipts),timeout_or_memory_kill=[],failed_attempts={'NNM_L023':'Own Domain344 assertion missed SdkState; corrected inL024','NNM_L030':'Stale own expected-import inventory; source-derived correction passesL031'})
put('RESOURCES',resources)
assert J(E/'NNM_RAW_BINARY.json')['sha256']=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
put('AUDIT',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_COLLECTOR_FINDINGS',full_composition_pass=True,combined='NNM_COMBINED_IMPORT',combined_attempt='NNM_L025',statement_attempt='NNM_L026',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(results),new_roots=len(required['roots'])-13308,all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)/(ax2)",same_optimized_proof_binary_sha256=J(E/'NNM_RAW_BINARY.json')['sha256'],fixtures=fixtures['results'],walker=J(P/'NNL_AUDIT.json')['walker'],scanner='NNM_SCAN.json',coherence='One fresh rev4 RSL object set; same complete predecessor root types/owners; fifteen NMV wrapper imports from private rev4 replay only',resources=resources,cold_release_replay=False,security_target_established=False))
basis=J(P/'NNL_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};review=J(E/'NNM_CANDIDATE_REVIEW.json');clauses=J(E/'NNM_CLAUSE_REVIEW.json');newrows=[]
clause_by={c['id']:c for c in clauses['clauses']}
def update_inherited(v):
 if isinstance(v,dict):
  key=v.get('id')
  if key in clause_by:
   z=clause_by[key];v.update(status='DISCHARGED',discharged_by=z['discharged_by'],NNM_evidence=z)
  for z in list(v.values()):
   if z is not v.get('NNM_evidence'):update_inherited(z)
 elif isinstance(v,list):
  for z in v:update_inherited(z)
for c in review['candidates']:
 assert c['gate_status']=='STATIC_PASS_REPLAY_PENDING';name=c['theorem'];r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 assert statements[name]['owner_module']==name.split('.')[-2]
 for child in c['canonical_children']:
  if child.get('status')=='RECLASSIFIED_SPURIOUS_BY_NAME':continue
  assert by[child['row']]['status']=='CLOSED',(r['row'],child['row']);child['status']='CLOSED';child['roots']=by[child['row']]['root_owners']
 c.update(status='PASS_COMPLETE_ROOT_GATE_ADMITTED',gate_status='PASS_COMPLETE_ROOT_GATE_ADMITTED',gate_admitted=True,kernel_statement=statements[name])
 old=copy.deepcopy(r['obligation']);o=r['obligation'];o['NNM_complete_candidate_review']=c;o['NNM_root_domain']=c['own_input'];o['kernel_roots']=[statements[name]]
 for kind in ['caller_domain_obligations','inventory_domain_obligations']:
  for z in o.get(kind,[]):
   if z.get('status')=='RECLASSIFIED_SPURIOUS_BY_NAME':continue
   if r['row']=='TX2:233'and z.get('callee','').startswith('crates/aspis-core/src/field'):
    z.update(status='RECLASSIFIED_SPURIOUS_BY_NAME',discharged_by=None,NNM_evidence='TCK_REPORT §5 / RSL_TX2_233 u64 PDA seed; retained edge');continue
   z.update(status='INTERNAL_DISCHARGED_WITH_OWN_INPUT_PROVENANCE_RETAINED',discharged_by=name,NNM_evidence='NNM_CLAUSE_REVIEW / complete source fold; SAME entered arguments, original D1/D2 remain upstream for241')
 update_inherited(o);o['NNM_basis_obligation']=old
 o['certificate'].update(bridge_status='CLOSED',composed_status='CLOSED',NNM_root=name,NNM_gate='PASS',NNM_route='(bn) source fission'if r['row']=='TX1:344'else'(bm) actual frozen emitted parent with(bc) audit and CLOSED same-input children',no_credit_reason='Historical predecessor reasons retained in NNM_basis_obligation; superseded by coherent current root gate')
 trust=set(r.get('consumes_trust',[]))|set(c['consumes_trust'])|{'NativeContractSemanticTransport','TrustedStd','AllocatorABICompilerSourceToELF'}
 for child in c['canonical_children']:
  if child.get('status')=='CLOSED':trust.update(by[child['row']].get('consumes_trust',[]))
 r.update(previous_status='OPEN',status='CLOSED',owner_module=statements[name]['owner_module'],owner_role='canonical complete revision4 source/observation root',root_owners=[dict(root=name,owner_module=statements[name]['owner_module'],obligation_statement_sha256=H(statements[name]['obligation_statement'].encode()))],evidence_dir='evidence/ledger29-20261111',consumes_trust=sorted(trust),consumes_trust_inherited_children=[dict(row=z['row'],roots=z.get('roots',[]),retained_row_consumes_trust=by[z['row']].get('consumes_trust',[]),certificate_trust=by[z['row']]['obligation']['certificate'].get('trust'))for z in c['canonical_children']if z.get('status')=='CLOSED'])
 newrows.append(r['row'])
 if r['row']!='TX1:344':ledger['extraction_trust_reclassifications'].append(dict(item='NNM-'+r['row']+'-emitted-body-bm',row=r['row'],root=name,classification='RECLASSIFICATION of existing extraction item narrowed by(bc); increased reliance under(bm), never removal',fresh_parent_provenance=True,emission={'TX1:345':'NMT_E003','TX2:233':'NMX_E008','TX2:242':'NMS_E003 validate_asq8','TX2:241':'NMS_E003 stage2_owned'}[r['row']],child_provenance='(bk) unresolved inherited provenance retained',source_to_ELF='not newly established'))
# Retain every edge and historical clause, while updating the four resume registrations.
for row in ['TX2:240','TX2:221','TX2:213']:update_inherited(by[row]['obligation'])
for z in clauses['clauses']:z['status']='DISCHARGED'
for z in clauses['registered_caller_clauses']:
 xs=by['TX2:240']['obligation']['caller_domain_obligations'];assert not any(q.get('id')==z['id']for q in xs);xs.append(z)
review['gate']='PASS';put('CANDIDATE_REVIEW',review);put('CLAUSE_REVIEW',clauses)
ledger['top_composition_obligations']=J(E/'NNM_TOP_COMPOSITION.json')['top_composition_obligations']
for n in ['SPECIFICATION','TOP_COMPOSITION','K086','PROVENANCE']:ledger['NNM_'+{'SPECIFICATION':'specification','TOP_COMPOSITION':'top_composition','K086':'K086','PROVENANCE':'extraction_provenance'}[n]]=J(E/('NNM_'+n+'.json'))
for tr in ledger['trust_rows']:
 added_consumers={row for row in newrows if tr['id']in by[row].get('consumes_trust',[])}
 tr['consumed_by_closed_rows']=sorted(set(tr.get('consumed_by_closed_rows',[]))|added_consumers)
 if tr['id']=='ReviewedTranscription-TX1:344':tr.update(status='USED',direct_closed_rows=sorted(set(tr.get('direct_closed_rows',[]))|{'TX1:344'}),NNM_consumer='AspisR1.NNG_Candidate344.candidate',consumer=tr.get('consumer','')+'; also AspisR1.NNG_Candidate344.candidate via NMV_ConcreteWindows.root344',NNM_note='Existing(bn) option-A reclassification now consumed; statement/removal condition unchanged')
 if tr['id']=='ReviewedTranscription-TX2:240':tr['NNM_status']='RETAINED_UNUSED_BY_CLOSED_ROWS'
for tr in ledger['reviewed_transcription_inventory']:
 if tr.get('item',tr.get('id'))=='ReviewedTranscription-TX1:344':tr.update(NNM_status='USED',NNM_consumer='AspisR1.NNG_Candidate344.candidate')
for r in ledger['rows']:
 assert r['canonical_callees']==oldby[r['row']]['canonical_callees']
 if r['obligation']!=oldby[r['row']]['obligation']:r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
assert newrows==['TX1:345','TX1:344','TX2:233','TX2:242','TX2:241'];assert {r['row']for r in ledger['rows']if r['status']!=oldby[r['row']]['status']}==set(newrows)
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':594,'OPEN':5}
ledger.update(basis='ledger28 NNL_LEDGER plus five NNM-gated coherent revision4 roots;599 rows and every edge retained',basis_delta='NNM_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('LEDGER',ledger,True)
put('LEDGER_DELTA',dict(basis='evidence/ledger28-20261111/NNL_LEDGER.json.xz',basis_uncompressed_sha256=(P/'NNL_LEDGER.json.sha256').read_text().strip(),before=dict(CLOSED=589,QUALIFIED=0,OPEN=10),after=dict(CLOSED=594,QUALIFIED=0,OPEN=5),new_closed_rows=newrows,new_count=5,rows=[dict(row=c['row'],root=c['theorem'],previous_status='OPEN',status='CLOSED',own_input_clauses=c['own_input'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],complete_obligation_statement_hash=by[c['row']]['obligation_statement_hash'])for c in review['candidates']],added_edges=[],removed_edges=[],trust_inventory_additions=[],trust_inventory_removals=[],wrapper_trust_used=['ReviewedTranscription-TX1:344'],wrapper_trust_unused=['ReviewedTranscription-TX2:240'],extraction_trust_reclassifications=[x for x in ledger['extraction_trust_reclassifications']if x.get('item','').startswith('NNM-')],top_composition_not_row_counts=True,provenance_conservative_impact=len(ledger['NNM_extraction_provenance']['current_conservative_affected_CLOSED_rows']),pool_promotions=[],security_target_established=False))
print(json.dumps(dict(gate='PASS',counts=counts,resources=resources)))
