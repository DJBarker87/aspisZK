"""Only additive active-at admission after strict immutable reuse and ax2 checks."""
from pathlib import Path
import json,lzma,hashlib,copy,types,subprocess,sys,time,resource
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];start=time.monotonic();sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text());put=lambda n,d:(E/n).write_text(json.dumps(d,indent=1)+'\n')
for name in ['NIJ_entry_check.py','NIJ_error_check.py','NIJ_active_check.py']:subprocess.run([sys.executable,str(E/name)],check=True)
rev='b5d4491a07b'
def prior(n):return json.loads(subprocess.check_output(['git','show',rev+':'+str((E/n).relative_to(R))],cwd=R))
delta=prior('NIJ_LEDGER_DELTA.json');closed=prior('NIJ_CLOSED.json');assert len(delta['new_closed_rows'])==3
base=json.loads(lzma.decompress((E.parent/'ledger10-20261106/NHO_LEDGER.json.xz').read_bytes()));by={r['row']:r for r in base['rows']}
v=(E/'NIJ_NFK_validate.py.txt').read_bytes();assert sha(v)==delta['unchanged_NFK_validator_sha256'];n=types.ModuleType('NIJ_active_NFK');n.__file__=str(E/'NIJ_NFK_validate.py.txt');exec(compile(v,n.__file__,'exec'),n.__dict__);n.BASE_CREDITS=base['NEZ_credits']
candidates={};certs={}
for root,prefix in [(E.parent/'slice-d-entry3-20261106','NHJ'),(E.parent/'slice-d-entry4-20261106','NHY')]:
 cc={c['id']:c for c in read(root/(prefix+'_CLOSED.json'))['functions']}
 for r in read(root/(prefix+'_LEDGER_DELTA.json'))['rows']:candidates[r['row']]=(prefix,copy.deepcopy(r));certs[r['row']]=cc[r['selected_claims'][0]]
cc={c['id']:c for c in closed['functions']}
for r in delta['rows']:candidates[r['row']]=('NIJ',copy.deepcopy(r));certs[r['row']]=cc[r['selected_claims'][0]]
raw=read(E/'NIJ_stage3_audit/proof2.json');fx=read(E/'NIJ_stage1_audit/fixtures.json');scan=read(E/'NIJ_stage3_audit/scan_summary.json');assert raw['exit_status']==0 and raw['same_optimized_binary_sha256']==fx['same_optimized_binary_sha256']
assert all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw['results'])
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
new=[];newc=[];denials=[]
for rid,version,op,pos,neg,child in [('TX2:194','V1','op30','NCF_K006','NCF_K007','TX2:193'),('TX2:196','V2','op29','NCF_K002','NCF_K003','TX2:195')]:
 r=copy.deepcopy(by[rid]);assert r['composed_status']=='OPEN' and not r['named_hypotheses'];claim='NIJ::active_'+version.lower();selected=candidates[child][1]['selected_claims'];assert selected==['NHY::retirement_'+version.lower()]
 for o in r['caller_domain_obligations']:
  same=('VerifierRegistryEntry'+version+'::') in o['callee'];o.update(status='CLOSED',callee_local_status='CLOSED' if same else 'EXCLUDED-TYPED-ALTERNATIVE',callee_claims=selected if same else [],discharged_by=claim+(': Exact self reference same typed record, all fields/u64 slots arbitrary. Actual NCF whole-body contract executes helper; NIJ_ActiveSlots.retirement_'+version.lower()+' composes CLOSED child without status/slot success premise.' if same else ': Conservative opposite-version alternative impossible at inherent typed &self call; exact frozen impl and whole-body root bind receiver. No callee claim selected for this alternative.'))
 c=dict(id=claim,subject=r['function'],route='retained actual whole-body pure Bool contract; canonical cohort retarget and exact typed child composition',model_theorem='NIJ_ActiveSlots.'+op+'_exact',root_domain='Every typed '+version+' record and every u64 slot; four status constructors exhaustive; no requires beyond true.',inner_hypotheses_remaining=[],native_passes=[pos],matched_controls=[neg],callee_laws=selected,source_association='NIJ_ACTIVE_ASSOCIATION.json / NIJ_active_check.py: original stage1 annotation/source/gate reconstructed to receipt hashes; frozen body unchanged; actual whole body and helper execute, no stub_verified selected. Historical default statement features revalidated by complete no-cfg reached body/type/constant parity; no cfg-if/libc or copy-dependent computation reached. No new Kani run or extraction claimed.',effects='Pure shared-reference Bool query, account fields/state unchanged; no allocation/syscall or pointer dispatch.',combined='NIJ_L050',audit=['NIJ_L051 raw proof2 and NFX; standard axioms, same calibrated optimized binary'],trust_reclassification='Existing P6/D188 compiler/native-contract semantic transport retained; no new runtime row.',root_model='AspisR1.RPx_Deployed.deployed; frozen3; L154 parameter')
 c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());r.update(composed_status='CLOSED',bridge_status='CLOSED-CONDITIONAL',selected_claims=[claim],open_transitive_dependencies=[],active_support_receipts=['evidence/native-u04d-20261028/'+pos+'/receipt.json'],composed_reason='Exact all-record/u64 native root plus canonical active model, typed no-retirement child domain and coherent ax2/NFX.')
 reasons=n.row_checks(r,by[rid],c)
 assert reasons==['NEZ K-2/K-3 active support denial'],reasons
 credit=next(x for x in base['NEZ_credits'] if x['receipt']==r['active_support_receipts'][0]);assert credit['k3_status']=='SUSPENDED'
 denials.append(dict(row=rid,status='OPEN',reasons=reasons,credit=credit,proposed_certificate=c))
put('NIJ_ACTIVE_REJECTED.json',dict(status='DENIED_UNCHANGED_NFK',rows=denials,native_budget_exhausted=True,no_suspended_receipt_restored=True))
# Retain the three admitted rows exactly. Add rejection checks and the new audit,
# never alter source/certificate predicates or restore suspended credit.
delta['checks_added']+=['active-at historical contracts denied by unchanged K-3 active-support predicate; no new credit','final SDK operation/write/drop/returned-vector support replay with standard ax2/NFX']
put('NIJ_LEDGER_DELTA.json',delta);put('NIJ_CLOSED.json',closed)
audit=prior('NIJ_AUDIT.json');audit['combined'].append('NIJ_L050');audit['roots']+=raw['results'];audit['scan']=scan;put('NIJ_AUDIT.json',audit)
put('NIJ_ACTIVE_VALIDATION.json',dict(status='PASS_REJECTION_CHECK',target='historical active-at source checks and unchanged suspended-receipt denial',exit_status=0,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=sha(Path(__file__).read_bytes()),wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A Python; formal ax2/NFX NIJ_L051',new_rows=0,cumulative_rows=3,denied_rows=['TX2:194','TX2:196']))
print('PASS denial checks: three cumulative rows; 366 CLOSED / 233 OPEN; zero complete paths')
