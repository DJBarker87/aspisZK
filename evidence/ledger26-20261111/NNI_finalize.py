"""Assign ledger credit only after every mandatory gate artifact is validated."""
from pathlib import Path
import json,lzma,hashlib,collections,copy,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'ledger25-20261111';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):
 if p.suffix=='.xz':
  b=lzma.decompress(p.read_bytes());assert H(b)==Path(str(p)[:-3]+'.sha256').read_text().strip();return json.loads(b)
 return json.loads(raw(p))
def put(n,x):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/('NNI_'+n+'.json')
 if n in ['LEDGER','KERNEL_STATEMENTS']or len(b)>20_000_000:Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(b)
required=J(E/'NNI_AUDIT_ROOTS.json');results=[];disagreements=[];plan=[]
for i,g in enumerate(required['groups']):
 mode='batch20-21'if i in [20,21]else'batch'+str(i);d=J(E/f'NNI_audit/{mode}/proof{i}.json');assert [r['root']for r in d['results']]==g
 results+=d['results'];plan.append(dict(group=i,mode=mode))
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
 assert d['exit_status']==(1 if any(not r['equal']for r in d['results'])else 0)
assert len(results)==len(required['roots'])==len({r['root']for r in results})==12599
assert {r['root']for r in disagreements}=={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
fx=J(E/'NNI_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==J(P/'NMQ_audit/fixtures/fixtures.json')['results'] and len(fx['results'])==8
sc=J(E/'NNI_audit/scan/scan.json');assert sc['exit_status']==0
scanrows=[json.loads(l)for l in raw(E/'NNI_LOADED_scan.jsonl').decode().splitlines()];scan=dict(status='PASS',exit_status=0,combined='NNI_COMBINED_IMPORT',modules=len(scanrows),dangling=sum(len(r['dangling'])for r in scanrows),canonical_duplicate_owners=sum(len(r['duplicate_owners'])for r in scanrows),import_mismatches=sum(not r['imports_match']for r in scanrows),cached_replicas=sum(len(r['cached_replicas'])for r in scanrows),retained_failed_scan='NNI_L054: source-derived expected import inventory incomplete; zero dangling/duplicate owners; repaired manifest is a changed input')
assert not(scan['dangling']or scan['canonical_duplicate_owners']or scan['import_mismatches']);put('SCAN',scan)
statements={}
for line in raw(E/'NNI_L010/stdout.log').decode().splitlines():
 if 'NNI_OWNER 'in line:
  r=json.loads(line.split('NNI_OWNER ',1)[1]);assert r['root']not in statements;statements[r['root']]=r
old=J(P/'NMQ_KERNEL_STATEMENTS.json.xz');assert set(statements)==set(required['roots']);assert all(statements.get(n)==v for n,v in old.items())
assert statements['AspisR1.NNG_Candidate136.candidate']['owner_module']=='NNG_Candidate136';assert statements['LIBB_PoolNoWrite.laws']['obligation_statement']=='NMV_NoWrite.PoolLaws LIBB_PoolLib.library'
put('KERNEL_STATEMENTS',statements);put('OWNER_COMPARISON',dict(status='PASS',previous=len(old),identical=len(old),new=len(statements)-len(old),wrong=[]))
entries=[json.loads(l)for l in(E/'NNI_ATTEMPTS.jsonl').read_text().splitlines()];receipts=[r for r in entries if 'exit_status'in r];assert len(receipts)==len({r['attempt']for r in receipts})<=60
nonzero=[]
for row in receipts:
 a=row['attempt'];r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and str(r['swaps'])=='0'
 assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
 checks=[q for q in entries if q.get('attempt')==a and q.get('event')=='share_check'];assert checks and checks[-1]['host']['count']<6
 if r['exit_status']:
  nonzero.append(a);assert a in ['NNI_L002','NNI_L007','NNI_L008','NNI_L054']or(r['kind']=='audit'and r['module'].startswith('batch'))
resources=dict(scopes=len(receipts),budget=60,unused=60-len(receipts),kinds=dict(collections.Counter(r['kind']for r in receipts)),wall_seconds=sum(r['wall_seconds']for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=sum(int(r['swaps'])for r in receipts),kani=0,extraction=0,aggregation16G_scopes=0,retained_nonzero_exits=nonzero,timeout_or_memory_kill=[],one_scope_at_a_time=True)
binary=J(E/'NNI_L006/NNI_ProofDriver_BINARY_PIN.json')['sha256'];assert binary==J(P/'NMQ_AUDIT.json')['same_optimized_proof_binary_sha256']
assert J(E/'NNI_PREDECESSOR_COMPARISON.json')['status']=='PASS' and J(E/'NNI_FINAL_HOST.json')['status']=='PASS'
put('RESOURCES',resources);put('AUDIT_GROUPS',dict(required=plan,all_required_roots=len(results),groups=len(plan),paired_groups=[20,21],pre_split_predecessor_shapes=True,new_groups_max120=True))
put('AUDIT',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_COLLECTOR_FINDINGS',full_composition_pass=True,combined='NNI_COMBINED_IMPORT',combined_attempt='NNI_L009',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(results),new_roots=len(statements)-len(old),raw_standard_axioms_only=True,all_required_raw_roots_present=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)/(ax2)",same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NNI_SCAN.json',walker=J(P/'NMQ_AUDIT.json')['walker'],resources=resources,cold_release_replay=False,security_target_established=False))
basis=J(P/'NMQ_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};review=J(E/'NNI_CANDIDATE_REVIEW.json');c136,c217=review['candidates'];assert c136['status']=='STATIC_REVIEW_PASS_GATE_PENDING'and c217['status']=='OPEN_FIDELITY_CONTROL_MISSING'
r=by['TX1:136'];assert r['status']=='OPEN'and r['obligation_statement_hash']==c136['basis_obligation_statement_hash'];assert all(next(q for q in ledger['rows']if q['transaction']=='TX1'and q['function']==c)['status']=='CLOSED'for c in r['canonical_callees'])
o=copy.deepcopy(r['obligation']);o['NNI_basis_obligation']=copy.deepcopy(o);o['NNI_complete_candidate_review']=c136;o['NNI_root_domain']=c136['own_input_clauses'];o['kernel_roots']=[statements[c136['candidate']]]
o['certificate'].update(bridge_status='CLOSED',composed_status='CLOSED',NNI_root=c136['candidate'],NNI_gate='PASS',NNI_route='(bm) actual fresh emitted verify_finish; exact canonical revision3 RowSpec; concrete library deterministic graphs; SAME argument and domain composition',no_credit_reason='Historical rejection superseded for136 only by the complete NNI gate; original retained in NNI_basis_obligation',NNI_trust='Existing extraction item (bm increased reliance), Std/runtime/native child method retained; no cryptographic trust added or removed')
for key in ['caller_domain_obligations','inventory_domain_obligations']:
 for c in o[key]:c.update(status='INTERNAL_DISCHARGED_WITH_OWN_INPUT_PROVENANCE_RETAINED',discharged_by=c136['candidate']+'; NNG_AllReached136/NNG_Packet136.closed install same-call graph/domain; finishInputDom remains at137, no hidden success/library premise')
r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module='NNG_Candidate136',owner_role='canonical complete136 actual-emission row packet',root_owners=[dict(root=c136['candidate'],owner_module='NNG_Candidate136',obligation_statement_sha256=H(statements[c136['candidate']]['obligation_statement'].encode()))],evidence_dir='evidence/ledger26-20261111',consumes_trust=['NativeContractSemanticTransport','TrustedStd','AllocatorABICompilerSourceToELF'],consumes_trust_inherited_children=[dict(row=c['row'],roots=c['roots'],certificate_trust=by[c['row']]['obligation']['certificate'].get('trust'),retained_row_consumes_trust=by[c['row']].get('consumes_trust',[]))for c in c136['canonical_children']])
parent=by['TX1:137'];parent['obligation']['NNI_parent_basis_obligation']=copy.deepcopy(parent['obligation']);parent['obligation']['NNI_explicit_child_domains']=J(E/'NNI_PARENT_CLAUSES.json')
parent['obligation']['caller_domain_obligations'].append(dict(id='NNI-own:TX1:137:TX1:136:finishInputDom',caller=parent['function'],callee=r['function'],required='LIB_VLib.library.finishInputDom a.public_ a.prefix_ a.transcript a.challenges at SAME reached verify_finish args',status='OPEN',discharged_by=None,reason='136 own-input clause;137 literal RowSpec not yet submitted; NNG caller-support laws do not close parent'))
by['TX2:217']['obligation']['NNI_candidate_review']=c217
# Retain every phantom edge; reclassify the precise clause by frozen source occurrence.
phantoms=[('TX2:233','TX2:016','M31::to_le_bytes','Frozen owned:293 is u64::to_le_bytes(checkpoint.checkpoint_sequence : u64), a PDA seed; RSL.u64le under(au), not a field child.'),('TX2:233','TX2:039','WideExact::to_le_bytes','Same u64 source occurrence; never WideExact::to_le_bytes; required NCS_R073 predicates are a name collision.'),('TX2:240','TX2:043','FibreIndex::get','Frozen owned:479 is Clock::get(), solana Sysvar::get, not FibreIndex::get; Event.clock/Env.clock/NMV_WindowClock consume existing RuntimeClockSlotBinding.')]
reclasses=[]
for caller,child,suffix,reason in phantoms:
 row=by[caller];callee=by[child]['function'];assert callee in row['canonical_callees'];entry=dict(caller=caller,callee=child,status='RECLASSIFIED_SPURIOUS_BY_NAME',edge_retained=True,discharged_by=None,reason=reason,evidence='TCK_REPORT.md §5; RSL_'+caller.replace(':','_')+'.lean')
 reclasses.append(entry)
 for kind in ['caller_domain_obligations','inventory_domain_obligations']:
  for c in row['obligation'][kind]:
   if c.get('callee')==callee or suffix in c.get('id',''):c.update(status='RECLASSIFIED_SPURIOUS_BY_NAME',discharged_by=None,NNI_reclassification=entry)
ledger['inventory_edge_reclassifications']+=reclasses
for id in ['TX2:241','TX2:240','TX2:221','TX2:213']:
 for c in by[id]['obligation']['caller_domain_obligations']:
  if c['id'].startswith('NLG-upstream:'):
   c.update(status='OPEN',discharged_by=None,NNI_pending_discharge='TX2:241 internal, only once canonical rev3 root241 is CLOSED in same gate; then resolve to that root Lean name',NNI_root0_excluded='Root0 remains TOP:G1c-B/TOP:R0rep, not covered by extents clause')
adds=J(E/'NNI_TRUST_ADDITIONS.json');ids={t['id']for t in ledger['trust_rows']}
for t in adds['additions']:
 assert t['id']not in ids;ledger['trust_rows'].append(copy.deepcopy(t));ledger['reviewed_transcription_inventory'].append(copy.deepcopy(t))
clock=next(t for t in ledger['trust_rows']if t['id']=='RuntimeClockSlotBinding');clock['NNI_consumer_addition']=adds['RuntimeClockSlotBinding_consumer_addition'];clock['NNI_statement_status_unchanged']=True
ledger['NNI_top_composition']=J(E/'NNI_TOP_COMPOSITION.json');poollaw=next(t for t in ledger['NNI_top_composition']['top_composition_obligations']if t['id']=='TOP:PoolLaws');assert 'LIBB_PoolNoWrite.laws'in required['roots']
poollaw.update(status='CLOSED',deliverable=dict(lean='LIBB_PoolNoWrite.laws',source_commit=subprocess.check_output(['git','log','-1','--format=%H','--','evidence/libb-20261111/LIBB_PoolNoWrite.lean'],text=True).strip()),extra_parameters=[],print_axioms=next(r['walked_axioms']for r in results if r['root']=='LIBB_PoolNoWrite.laws'),credit='Exact concrete PoolLaws LIBB_PoolLib.library term; no parameter, compiled combined and raw ax2. Host G2/folds remain uninstantiated and OPEN.')
ledger['NNI_specification']=J(E/'NNI_SPECIFICATION.json');prov=J(E/'NNI_PROVENANCE.json');assert prov['gate_reachability_used']and len(prov['current_conservative_affected_CLOSED_rows'])==563;ledger['NNI_extraction_provenance']=prov
for z in ledger['rows']:
 assert z['canonical_callees']==oldby[z['row']]['canonical_callees']
 if z['obligation']!=oldby[z['row']]['obligation']:z['obligation_statement_hash']=H(json.dumps(z['obligation'],sort_keys=True,separators=(',',':')).encode())
assert {z['row']for z in ledger['rows']if z['status']!=oldby[z['row']]['status']}=={'TX1:136'};counts=dict(collections.Counter(z['status']for z in ledger['rows']));assert counts=={'CLOSED':583,'OPEN':16}
ledger.update(basis='ledger25 NMQ_LEDGER plus NNI-gated TX1:136 only;599 rows/every edge retained',basis_delta='NNI_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('LEDGER',ledger);put('LEDGER_DELTA',dict(basis='evidence/ledger25-20261111/NMQ_LEDGER.json.xz',basis_uncompressed_sha256=(P/'NMQ_LEDGER.json.sha256').read_text().strip(),before=dict(CLOSED=582,QUALIFIED=0,OPEN=17),after=dict(CLOSED=583,QUALIFIED=0,OPEN=16),new_closed_rows=['TX1:136'],new_count=1,rows=[dict(row='TX1:136',previous_status='OPEN',status='CLOSED',root=c136['candidate'],basis_obligation_statement_hash=c136['basis_obligation_statement_hash'],complete_obligation_statement_hash=r['obligation_statement_hash'],own_input_clauses=c136['own_input_clauses'])],rejected_candidates=[dict(row='TX2:217',status='OPEN',blocker=c217['exact_blocker'])],added_edges=[],removed_edges=[],edge_reclassifications=reclasses,explicit_parent_clause_updates=J(E/'NNI_PARENT_CLAUSES.json'),trust_inventory_additions=adds['additions'],trust_inventory_removals=[],cryptographic_trust_changes=False,top_composition_not_row_counts=True,top_field_closed=['TOP:PoolLaws'],provenance_conservative_impact=563,pool_promotions=[],security_target_established=False))
c136.update(status='PASS_COMPLETE_ROOT_GATE_ADMITTED',gate_admitted=True,kernel_statement=statements[c136['candidate']]);c217.update(kernel_statement=statements[c217['candidate']],reference_replay='PASS; no native credit because fidelity gate incomplete');review.update(gate='PASS',security_target_established=False);put('CANDIDATE_REVIEW',review)
put('TOP_COMPOSITION',ledger['NNI_top_composition'])
# Portable selected evidence for report generation; no huge uncompressed ledger.
from NNI_report import report
report(ledger,resources)
print(json.dumps(dict(gate='PASS',CLOSED=583,QUALIFIED=0,OPEN=16,roots=len(results),modules=scan['modules'],scopes=len(receipts))))
