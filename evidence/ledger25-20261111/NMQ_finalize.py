"""Promote only064, only after the complete serial gate and final retention."""
from pathlib import Path
import json,lzma,hashlib,collections,copy,subprocess,sys
sys.dont_write_bytecode=True
from NMQ_report import report
E=Path(__file__).resolve().parent;P=E.parent/'ledger24-20261110';Q=E.parent/'tx2-entry5-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):
 if p.suffix=='.xz':
  b=lzma.decompress(p.read_bytes());assert H(b)==Path(str(p)[:-3]+'.sha256').read_text().strip();return json.loads(b)
 return json.loads(raw(p))
def put(n,x):
 b=(json.dumps(x,sort_keys=True,indent=1)+'\n').encode();p=E/n
 if n in ['NMQ_LEDGER.json','NMQ_KERNEL_STATEMENTS.json']or len(b)>20_000_000:
  Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(b)
required=J(E/'NMQ_AUDIT_ROOTS.json');results=[];disagreements=[];nonzero=[];groups=[]
for i,g in enumerate(required['groups']):
 mode='batch20-21'if i in [20,21]else'batch'+str(i)
 d=J(E/f'NMQ_audit/{mode}/proof{i}.json');assert [r['root']for r in d['results']]==g;results+=d['results'];groups.append(dict(group=i,mode=mode))
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
 assert d['exit_status']==(1 if any(not r['equal']for r in d['results'])else 0)
assert len(results)==len(required['roots'])==len({r['root']for r in results})==11401
assert {r['root']for r in disagreements}=={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
fx=J(E/'NMQ_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==J(P/'NLX_audit/fixtures/fixtures.json')['results'] and len(fx['results'])==8
scanrows=[json.loads(l)for l in raw(E/'NMQ_LOADED_scan.jsonl').decode().splitlines()];sr=J(E/'NMQ_audit/scan/scan.json');assert sr['exit_status']==0
scan=dict(status='PASS',exit_status=0,attempt='NMQ_L039',scanner='NFX complete canonical loaded private environment',combined='NMQ_COMBINED_IMPORT',modules=len(scanrows),dangling=sum(len(r['dangling'])for r in scanrows),canonical_duplicate_owners=sum(len(r['duplicate_owners'])for r in scanrows),import_mismatches=sum(not r['imports_match']for r in scanrows),cached_replicas=sum(len(r.get('cached_replicas',[]))for r in scanrows),identical_cache_replicas_are_not_duplicate_owners=True)
assert not(scan['dangling']or scan['canonical_duplicate_owners']or scan['import_mismatches']);put('NMQ_SCAN.json',scan)
statements={}
for line in raw(E/'NMQ_L006/stdout.log').decode().splitlines():
 if 'NMQ_OWNER 'in line:
  x=json.loads(line.split('NMQ_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x
old=J(P/'NLX_KERNEL_STATEMENTS.json.xz');assert set(statements)==set(required['roots']) and all(statements.get(n)==v for n,v in old.items())
assert statements['NMN_064.root']['owner_module']=='NMN_064';put('NMQ_KERNEL_STATEMENTS.json',statements);put('NMQ_OWNER_COMPARISON.json',dict(status='PASS',previous=len(old),identical=len(old),new=len(statements)-len(old),wrong=[]))
entries=[json.loads(l)for l in(E/'NMQ_ATTEMPTS.jsonl').read_text().splitlines()];rs=[r for r in entries if 'exit_status'in r];assert len(rs)==len({r['attempt']for r in rs})==40
for r in rs:
 a=r['attempt'];rc=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and str(rc['swaps'])=='0'
 if r['exit_status']!=0:nonzero.append(a);assert r['kind']=='audit' and r['module'].startswith('batch')
 assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
 checks=[x for x in entries if x.get('attempt')==a and x.get('event')=='share_check'];assert checks and checks[-1]['host']['count']<2
resources=dict(scopes=40,complete_receipts=40,unused_scopes=0,kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),kani=0,extraction=0,aggregation16G_scopes=0,retained_nonzero_audit_exits=nonzero,retained_timeout_attempts=[],max_cgroup_memory_peak_bytes=max(int(J(E/r['attempt']/'receipt.json')['cgroup_memory_peak_bytes'])for r in rs))
binary=J(E/'NMQ_L005/NMQ_ProofDriver_BINARY_PIN.json')['sha256'];assert binary==J(P/'NLX_AUDIT.json')['same_optimized_proof_binary_sha256']
for r in rs:
 p=E/r['attempt']/'NMQ_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
assert J(E/'NMQ_PREDECESSOR_COMPARISON.json')['status']=='PASS' and J(E/'NMQ_FINAL_HOST.json')['status']=='PASS'
review=J(E/'NMQ_CANDIDATE_REVIEW.json');assert review['primary_root']=='NMN_064.root' and not review['withdrawn_root_credit']
put('NMQ_RESOURCES.json',resources);put('NMQ_AUDIT_GROUPS.json',dict(required=groups,groups=33,scopes_for_root_walks=32,pre_split_ledger24_L023=True,paired_groups=[20,21],all_required_roots=11401))
put('NMQ_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_COLLECTOR_FINDINGS',full_composition_pass=True,combined='NMQ_COMBINED_IMPORT',combined_attempt='NMQ_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(results),new_roots=len(statements)-len(old),raw_standard_axioms_only=True,all_required_raw_roots_present=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)/(ax2)",retained_nonzero_audit_exits=nonzero,root_groups=len(groups),same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NMQ_SCAN.json',walker=J(P/'NLX_AUDIT.json')['walker'],resources=resources,cold_release_replay=False,security_target_established=False))
basis=J(P/'NLX_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']};oldby={r['row']:r for r in basis['rows']};r=by['TX2:064'];assert r['status']=='OPEN' and r['obligation_statement_hash']==review['basis_obligation_statement_hash']
assert all(next(z for z in ledger['rows']if z['transaction']=='TX2'and z['function']==c)['status']=='CLOSED'for c in r['canonical_callees'])
o=copy.deepcopy(r['obligation']);o['NMQ_basis_obligation']=copy.deepcopy(r['obligation']);o['NMQ_complete_clause_review']=J(E/'NMQ_CLAUSE_REVIEW.json');o['NMQ_hypothesis_inventory']=review['hypothesis_inventory'];o['NMQ_root_domain']=review['own_argument_clauses'];o['NMQ_root0_decision']=review['root0_decision'];o['kernel_roots']=[statements['NMN_064.root']]
o['certificate'].update(bridge_status='CLOSED',composed_status='CLOSED',NMQ_provider='NMN',NMQ_root='NMN_064.root',NMQ_gate='PASS',NMQ_route='bl whole actual-parent native G with full Result havocs, SAME arguments and Lean canonical child composition',NMQ_trust='Existing P6/D188 option-A native semantic transport RECLASSIFICATION; no removal',NMQ_no_new_native_or_extraction_run=True)
for c in o['caller_domain_obligations']:
 c.update(status='INTERNAL_SUPPLIED_FROM_OWN_INPUT_CLAUSE'if c['id'].startswith('NLX-bf:')else'INTERNAL_DISCHARGED',discharged_by='NMN_064.root; NMQ_CLAUSE_REVIEW.json distinguishes supplied bf2 own-input predicates retained at OPEN241 from internally derived SAME child laws and nested aq2/bl4 cuts')
for c in o['inventory_domain_obligations']:c.update(status='INTERNAL_DISCHARGED_WITH_CALLER_PROVENANCE_RETAINED',discharged_by='NMN_064.root; four original-input bf2 clauses remain explicitly at241; NMF accepted-headline Root0 OR existing collision occurrence')
r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module='NMN_064',owner_role='canonical complete064 row packet; all Result/error/stopped prefixes',root_owners=[dict(root='NMN_064.root',owner_module='NMN_064',obligation_statement_sha256=H(statements['NMN_064.root']['obligation_statement'].encode()))],evidence_dir='evidence/ledger25-20261111')
par=by['TX2:241'];assert par['status']=='OPEN';par['obligation']['NMQ_parent_basis_obligation']=copy.deepcopy(oldby['TX2:241']['obligation']);parent=J(E/'NMQ_PARENT_CLAUSES.json');par['obligation']['NMQ_explicit_child_domains']=parent
for i,c in enumerate(parent['clauses']):par['obligation']['caller_domain_obligations'].append(dict(id='NMQ-bf:TX2:241:TX2:064:'+str(i),caller=par['function'],callee=r['function'],required=c['predicate'],classification=c['classification'],status='OPEN',discharged_by=None,reason='Original SAME getter/range/encoder args must be installed by241; NMF occurrence alternative supplies Root0 at accepted headline only'))
for z in ledger['rows']:
 prior=oldby[z['row']];assert z['canonical_callees']==prior['canonical_callees']
 if z['obligation']!=prior['obligation']:z['obligation_statement_hash']=H(json.dumps(z['obligation'],sort_keys=True,separators=(',',':')).encode())
rt=dict(item='NMN-TX2:064-native-contract-semantic-transport',row='TX2:064',root='NMN_064.root',classification='existing P6/D188 option-A native contract semantic transport RECLASSIFICATION, never removal',scope='Actual frozen064, full arbitrary original buffers/full child Results; SAME recorded arguments; prefix-only stopped common',provider='NMN')
ledger.setdefault('native_transport_reclassifications',[]).append(rt)
trust=J(E/'NMQ_TRUST_INVENTORY.json');ledger['trust_rows']+=trust['aggregate_additions'];ledger['NMQ_complete_trust_appendix']=trust
next(t for t in ledger['trust_rows']if t['id']=='NativeContractSemanticTransport')['direct_closed_rows'].append('TX2:064')
prov=J(E/'NMQ_PROVENANCE.json');ledger['NMQ_extraction_provenance']=prov
ledger['NMQ_inventory_notes']='Inherited stale OPEN labels/snapshots remain historical. Root0 provenance previously owed by064 is now an explicit own-input clause at OPEN241, supported at the SAME accepted headline occurrence by NMF; NLT_Root never gets credit.'
counts=dict(collections.Counter(z['status']for z in ledger['rows']));assert counts=={'CLOSED':582,'OPEN':17}
assert {z['row']for z in ledger['rows']if z['status']!=oldby[z['row']]['status']}=={'TX2:064'}
assert len(prov['current_conservative_affected_CLOSED_rows'])==562 and all(by[id]['status']=='CLOSED'for id in prov['current_conservative_affected_CLOSED_rows'])
ledger.update(basis='ledger24 NLX_LEDGER plus NMQ-gated NMN_064.root only;599 rows/every edge retained',basis_delta='NMQ_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NMQ_LEDGER.json',ledger)
put('NMQ_LEDGER_DELTA.json',dict(basis='evidence/ledger24-20261110/NLX_LEDGER.json.xz',basis_uncompressed_sha256=(P/'NLX_LEDGER.json.sha256').read_text().strip(),before=dict(CLOSED=581,QUALIFIED=0,OPEN=18),after=dict(CLOSED=582,QUALIFIED=0,OPEN=17),new_closed_rows=['TX2:064'],new_count=1,rows=[dict(row='TX2:064',previous_status='OPEN',status='CLOSED',primary_root='NMN_064.root',owner_module='NMN_064',basis_obligation_statement_hash=review['basis_obligation_statement_hash'],complete_obligation_statement_hash=r['obligation_statement_hash'],domain=review['own_argument_clauses'])],root0_decision=review['root0_decision'],explicit_parent_clause_updates=parent,added_edges=[],removed_edges=[],no_other_status_change=True,no_double_count=True,native_transport_reclassifications=[rt],trust_inventory_additions=trust['aggregate_additions'],trust_inventory_removals=[],runtime_changes_beyond_recording_lead_additions=False,cryptographic_trust_changes=False,pool_promotions=[],provenance_conservative_impact=562,security_target_established=False))
review.update(status='PASS_COMPLETE_ROOT_GATE_ADMITTED',gate_admitted=True,kernel_statement=statements['NMN_064.root']);put('NMQ_CANDIDATE_REVIEW.json',review)
report(ledger,resources)
print(json.dumps(dict(gate='PASS',CLOSED=582,QUALIFIED=0,OPEN=17,modules=scan['modules'],roots=len(results),conservative_provenance_impact=562)))
