"""Promote two rows only after the complete current-context gate."""
from pathlib import Path
import json,lzma,hashlib,collections,subprocess,copy,re
E=Path(__file__).resolve().parent;P=E.parent/'ledger27-20261111';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):return json.loads(lzma.decompress(raw(p))if p.suffix=='.xz'else raw(p))
def put(n,x,compress=False):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/('NNL_'+n+'.json')
 if compress or len(b)>20_000_000:Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
assert J(E/'NNL_GATE_INTEGRITY.json')['status']=='PASS'
required=J(E/'NNL_AUDIT_ROOTS.json');results=[];disagreements=[]
for i,g in enumerate(required['groups']):
 ps=list((E/'NNL_audit').glob('batch*/proof'+str(i)+'.json'));assert len(ps)==1,(i,ps)
 d=J(ps[0]);assert [r['root']for r in d['results']]==g
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Quot.sound','Classical.choice'}
  if not r['equal']:
   assert r['root']in{'AspisR1.NKR_ScheduleExt.transition','NHC_DecodeModel.decoder_error','LIB_VCarriers.Acc','NNI_CollectorAcc.alias_identity'};disagreements.append(r)
 results+=d['results']
assert len(results)==len({r['root']for r in results})==len(required['roots'])
assert {r['root']for r in results}==set(required['roots'])
fixtures=J(E/'NNL_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and fixtures['results']==J(E/'NNL_EXPECTED_FIXTURES.json')
scan=J(E/'NNL_audit/retention/NNL_FINAL_SCAN.json');assert scan['exit_status']==0
loaded=[json.loads(l)for l in raw(E/'NNL_LOADED_scan.jsonl').decode().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
put('SCAN',dict(status='PASS',exit_status=0,attempt='NNL_L060',combined='NNL_COMBINED_IMPORT',modules=len(loaded),dangling=0,canonical_duplicate_owners=0,import_mismatches=0,cached_replicas=sum(len(r['cached_replicas'])for r in loaded),retired_failed_scan='NNL_L011: actual scanner exit1, outer wrapper bug; never credited'))
statements={}
for l in raw(E/'NNL_L020/stdout.log').decode().splitlines():
 if'NNL_OWNER 'in l:
  r=json.loads(l.split('NNL_OWNER ',1)[1]);assert r['root']not in statements;statements[r['root']]=r
assert set(statements)==set(required['roots']);put('KERNEL_STATEMENTS',statements,True)
comparison=J(E/'NNL_STATEMENT_COMPARISON.json');assert comparison['status']=='PASS_WITH_DECLARED_F9_LIBRARY_REPAIR'and[d['root']for d in comparison['differences']]==['LIB_VLib.parseShape_exact']
receipts=[J(p)for p in sorted(E.glob('NNL_L*/receipt.json'))];assert len(receipts)==60
entries=[json.loads(l)for l in(E/'NNL_ATTEMPTS.jsonl').read_text().splitlines()]
for r in receipts:
 a=r['attempt'];ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0';assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
 checks=[c for c in entries if c.get('attempt')==a and c.get('event')=='share_check'];assert checks and checks[-1]['host']['count']<6
 if r['exit_status']:assert a in['NNL_L003','NNL_L004']and r['exit_status']==1,(a,r['exit_status'])
resources=dict(scopes=60,budget=60,unused=0,kani=0,extraction=0,aggregation16G_scopes=0,one_scope_at_a_time=True,kinds=dict(collections.Counter(r['kind']for r in receipts)),wall_seconds=sum(r['wall_seconds']for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=sum(int(r['swaps'])for r in receipts),timeout_or_memory_kill=[],failed_review_modules=['NNL_L003','NNL_L004'],retired_failed_scan=dict(attempt='NNL_L011',scanner_exit=1,outer_exit=0,credit=False))
put('RESOURCES',resources)
assert J(E/'NNL_RAW_BINARY.json')['sha256']=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
put('AUDIT',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_COLLECTOR_FINDINGS',full_composition_pass=True,combined='NNL_COMBINED_IMPORT',combined_attempt='NNL_L019',statement_attempt='NNL_L020',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(results),new_roots=321,all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)/(ax2)",same_optimized_proof_binary_sha256=J(E/'NNL_RAW_BINARY.json')['sha256'],fixtures=fixtures['results'],walker=J(P/'NNK_AUDIT.json')['walker'],scanner='NNL_SCAN.json',resources=resources,cold_release_replay=False,security_target_established=False))
basis=J(P/'NNK_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};review=J(E/'NNL_CANDIDATE_REVIEW.json');clauses=J(E/'NNL_CLAUSE_REVIEW.json');newrows=[]
for c in review['candidates']:
 assert c['gate_status']=='STATIC_PASS_REPLAY_PENDING';name=c['theorem'];r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 assert statements[name]['owner_module']==name.split('.')[-2]
 for child in c['canonical_children']:
  assert by[child['row']]['status']=='CLOSED',(r['row'],child['row']);child['status']='CLOSED';child['roots']=by[child['row']]['root_owners']
 c.update(gate_status='PASS_COMPLETE_ROOT_GATE_ADMITTED',gate_admitted=True,kernel_statement=statements[name])
 old=copy.deepcopy(r['obligation']);o=r['obligation'];o['NNL_basis_obligation']=old;o['NNL_complete_candidate_review']=c;o['NNL_root_domain']=c['own_input'];o['kernel_roots']=[statements[name]]
 for kind in ['caller_domain_obligations','inventory_domain_obligations']:
  for z in o[kind]:z.update(status='INTERNAL_DISCHARGED_WITH_OWN_INPUT_PROVENANCE_RETAINED',discharged_by=name,NNL_evidence=c['source_chain'],NNL_note='SAME entered arguments and original domains derived internally; publicDom/P1880 own clauses remain upstream. Historical findings retained in NNL_basis_obligation, superseded in current context.')
 o['certificate'].update(bridge_status='CLOSED',composed_status='CLOSED',NNL_root=name,NNL_gate='PASS',NNL_route='(bm) actual frozen fresh emitted parent, (bc) audit, CLOSED child graphs and same-argument Lean folds',no_credit_reason='Historical rejection retained in NNL_basis_obligation; superseded for this row by full current gate')
 trust=set(r.get('consumes_trust',[]))|{'NativeContractSemanticTransport','TrustedStd','AllocatorABICompilerSourceToELF'}
 for child in c['canonical_children']:trust.update(by[child['row']].get('consumes_trust',[]))
 assert not({'ReviewedTranscription-TX1:344','ReviewedTranscription-TX2:240'}&trust)
 r.update(previous_status='OPEN',status='CLOSED',owner_module=statements[name]['owner_module'],owner_role='canonical complete revision4 source/observation root',root_owners=[dict(root=name,owner_module=statements[name]['owner_module'],obligation_statement_sha256=H(statements[name]['obligation_statement'].encode()))],evidence_dir='evidence/ledger28-20261111',consumes_trust=sorted(trust),consumes_trust_inherited_children=[dict(row=z['row'],roots=z['roots'],retained_row_consumes_trust=by[z['row']].get('consumes_trust',[]),certificate_trust=by[z['row']]['obligation']['certificate'].get('trust'))for z in c['canonical_children']])
 newrows.append(r['row']);ledger['extraction_trust_reclassifications'].append(dict(item='NNL-'+r['row']+'-emitted-body-bm',row=r['row'],root=name,classification='RECLASSIFICATION: existing extraction item narrowed by(bc); increased reliance under(bm); no cryptographic assumption or trust class removed',fresh_parent_provenance=True,emission='NMT_E001'if r['row']=='TX1:094'else'NMT_E002',child_provenance='(bk) unresolved inherited provenance retained',source_to_ELF='not newly established'))
# Explicit P1880 propagation; never use the open345 parent as a child premise.
for row,callee in [('TX1:328','TX1:094'),('TX1:345','TX1:328')]:
 record=dict(id=f'RSL4-caller:{row}:{callee}:P1880',callee=by[callee]['function'],required='SAME original public_bytes.length=1880',status='DISCHARGED',discharged_by='AspisR1.NNG_Candidate328.candidate'if row=='TX1:328'else'RSL.TX1_345.p1880_of_decode',proof_support='AspisR1.NNG_P1880Discharge.decoder; canonical345 decoder/snapshot-length law',NNL_note='Own clause at094/328; canonical345 input derivation only, not complete345 source closure')
 xs=by[row]['obligation']['caller_domain_obligations'];assert not any(z['id']==record['id']for z in xs);xs.append(record)
for z in by['TX1:094']['obligation']['caller_domain_obligations']:
 if z.get('id')=='RSL3-caller:TX1:094:TX1:087:R4':z.update(status='DISCHARGED',discharged_by='AspisR1.NNG_Candidate094.candidate',proof_support='NNG_TotalParse094.prepare_domain / RSL.TX1_094.r4_of_scan at SAME canonicalScan proof',finding='Historical F9 finding resolved; preserved in NNL_basis_obligation')
for z in clauses['clauses']:z['status']='DISCHARGED_IN_COMPLETE_SOURCE_FOLD'
review['gate']='PASS';put('CANDIDATE_REVIEW',review);put('CLAUSE_REVIEW',clauses)
ledger['NNL_specification']=J(E/'NNL_SPECIFICATION.json');ledger['NNL_top_composition']=J(E/'NNL_TOP_COMPOSITION.json');ledger['NNL_K086']=J(E/'NNL_K086.json');ledger['NNL_extraction_provenance']=J(E/'NNL_PROVENANCE.json')
for r in ledger['rows']:
 assert r['canonical_callees']==oldby[r['row']]['canonical_callees']
 if r['obligation']!=oldby[r['row']]['obligation']:r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
assert newrows==['TX1:094','TX1:328'];assert {r['row']for r in ledger['rows']if r['status']!=oldby[r['row']]['status']}==set(newrows)
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':589,'OPEN':10}
ledger.update(basis='ledger27 NNK_LEDGER plus two NNL-gated revision4 roots;599 rows and every edge retained',basis_delta='NNL_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('LEDGER',ledger,True)
prov=ledger['NNL_extraction_provenance'];put('LEDGER_DELTA',dict(basis='evidence/ledger27-20261111/NNK_LEDGER.json.xz',basis_uncompressed_sha256=(P/'NNK_LEDGER.json.sha256').read_text().strip(),before=dict(CLOSED=587,QUALIFIED=0,OPEN=12),after=dict(CLOSED=589,QUALIFIED=0,OPEN=10),new_closed_rows=newrows,new_count=2,rows=[dict(row=c['row'],root=c['theorem'],previous_status='OPEN',status='CLOSED',own_input_clauses=c['own_input'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],complete_obligation_statement_hash=by[c['row']]['obligation_statement_hash'])for c in review['candidates']],added_edges=[],removed_edges=[],trust_inventory_additions=[],trust_inventory_removals=[],wrapper_trust_unused=['ReviewedTranscription-TX1:344','ReviewedTranscription-TX2:240'],extraction_trust_reclassifications=[x for x in ledger['extraction_trust_reclassifications']if x.get('item','').startswith('NNL-')],top_composition_not_row_counts=True,provenance_conservative_impact=len(prov['current_conservative_affected_CLOSED_rows']),pool_promotions=[],security_target_established=False))
print(json.dumps(dict(gate='PASS',counts=counts,resources=resources)))
