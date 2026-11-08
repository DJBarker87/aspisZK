"""Strict no-promotion output when the full required raw audit is incomplete."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections,copy,re
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
subprocess.run(['python3',str(E/'NNM_prepare.py'),'--check'],check=True)
required=J(E/'NNM_AUDIT_ROOTS.json');results={};finished_groups=[];failed_groups=[]
for i,g in enumerate(required['groups']):
 ps=list((E/'NNM_audit').glob('batch*/proof'+str(i)+'.json'))
 if not ps:continue
 assert len(ps)==1,(i,ps)
 d=J(ps[0]);assert [r['root']for r in d['results']]==g
 assert d['exit_status']==0 or(d['exit_status']==1 and any(not r['equal']for r in d['results']))
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Quot.sound','Classical.choice'}
  if not r['equal']:assert r['root']in{'AspisR1.NKR_ScheduleExt.transition','NHC_DecodeModel.decoder_error','LIB_VCarriers.Acc','NNI_CollectorAcc.alias_identity'}
  assert r['root']not in results;results[r['root']]=r
 finished_groups.append(i)
missing=sorted(set(required['roots'])-set(results));assert missing,'Use the full finalizer when coverage is complete'
statements=J(E/'NNM_KERNEL_STATEMENTS.json');missing_details=[dict(root=r,owner_module=statements[r]['owner_module'],required='Current combined-context raw ax2 result; no credit from historical/supplier result')for r in missing]
put('MISSING_RAW_ROOTS',dict(status='OPEN',count=len(missing),roots=missing_details))
receipts=[J(p)for p in sorted(E.glob('NNM_L*/receipt.json'))];assert len(receipts)==60
entries=[json.loads(l)for l in(E/'NNM_ATTEMPTS.jsonl').read_text().splitlines()]
for r in receipts:
 a=r['attempt'];ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0';assert any(J(p)['free']>=40_000_000_000 for p in E.glob(a+'-disk*.json'))
 checks=[c for c in entries if c.get('attempt')==a and c.get('event')=='share_check'];assert checks and checks[-1]['host']['count']<6
 if r['exit_status']:assert isinstance(r['exit_status'],int)
resources=dict(scopes=60,budget=60,unused=0,kani=0,extraction=0,aggregation16G_scopes=0,one_scope_at_a_time=True,kinds=dict(collections.Counter(r['kind']for r in receipts)),wall_seconds=sum(r['wall_seconds']for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=sum(int(r['swaps'])for r in receipts),failed_attempts=[dict(attempt=r['attempt'],target=r['module'],exit=r['exit_status'],wall_seconds=r['wall_seconds'])for r in receipts if r['exit_status']],limits_raised=False,timeout_raised=False)
put('RESOURCES',resources)
scan=J(E/'NNM_audit/scan/scan.json');assert scan['exit_status']==0
loaded=[json.loads(l)for l in raw(E/'NNM_LOADED_scan.jsonl').decode().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
put('SCAN',dict(status='PASS',exit_status=0,attempt='NNM_L031',modules=len(loaded),dangling=0,canonical_duplicate_owners=0,import_mismatches=0,cached_replicas=sum(len(r['cached_replicas'])for r in loaded),retired_failed_scan='NNM_L030 independent source-derived inventory repair retained'))
assert J(E/'NNM_GATE_INTEGRITY.json')['status']==J(E/'NNM_PREDECESSOR_COMPARISON.json')['status']=='PASS'
fixtures=J(E/'NNM_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and fixtures['results']==J(P/'NNL_audit/fixtures/fixtures.json')['results']
put('AUDIT',dict(status='INCOMPLETE_NO_ROW_CREDIT',full_composition_pass=False,combined='NNM_COMBINED_IMPORT',combined_attempt='NNM_L025',statement_attempt='NNM_L026',required_roots=len(required['roots']),completed_roots=len(results),missing_roots=len(missing),missing_manifest='NNM_MISSING_RAW_ROOTS.json',finished_groups=finished_groups,completed_raw_standard_only=True,axioms=sorted({a for r in results.values()for a in r['walked_axioms']}),collect_axioms_disagreements=[r for r in results.values()if not r['equal']],same_optimized_proof_binary_sha256=J(E/'NNM_RAW_BINARY.json')['sha256'],fixtures=fixtures['results'],walker=J(P/'NNL_AUDIT.json')['walker'],scanner='NNM_SCAN.json',resources=resources,security_target_established=False,cold_release_replay=False,explanation='Aggregate audit windows exceeded180s; exact failure receipts are retained. L052 completed42 then unfinished43 isolated successfully; L057185-root aggregate split by graph-size estimates. Last three scopes prioritize candidates and maximize remaining coverage; strict full required-root set retained. No missing root substituted by historical evidence.'))
review=J(E/'NNM_CANDIDATE_REVIEW.json');clauses=J(E/'NNM_CLAUSE_REVIEW.json')
for c in review['candidates']:
 c.update(gate_admitted=False,gate_status='NOT_ADMITTED_FULL_GATE_INCOMPLETE',current_raw_result=results.get(c['theorem']),kernel_statement=statements[c['theorem']],exact_blocker='NNM_MISSING_RAW_ROOTS.json: complete current-context raw gate missing; no row promotion despite static/source/type passes')
review['gate']='INCOMPLETE';put('CANDIDATE_REVIEW',review)
clauses['gate']='INCOMPLETE';clauses['current_ledger_note']='Candidate internal dispositions retained, but NLG registrations remain OPEN in ledger until241 is CLOSED in a complete same gate.';put('CLAUSE_REVIEW',clauses)
# Recompute lexical candidate impact only if the current raw reachability exists.
if all(c['theorem']in results for c in review['candidates']):
 subprocess.run(['python3',str(E/'NNM_provenance.py')],check=True);prov=J(E/'NNM_PROVENANCE.json')
else:
 prov=J(P/'NNL_PROVENANCE.json');prov['NNM_candidate_provenance']='Not all candidate current raw reachability available; no new impact claim'
oldprov=J(P/'NNL_PROVENANCE.json');prov['candidate_potential_impact_if_promoted']=prov.get('new_closed_impact_if_promoted');prov['current_conservative_affected_CLOSED_rows']=oldprov['current_conservative_affected_CLOSED_rows'];prov['NNM_no_promotions']=True;put('PROVENANCE',prov)
basis=J(P/'NNL_LEDGER.json.xz');ledger=copy.deepcopy(basis);by={r['row']:r for r in ledger['rows']}
for c in review['candidates']:
 r=by[c['row']];assert r['status']=='OPEN';r['obligation']['NNM_reviewed_candidate_not_credited']=c
for z in clauses['registered_caller_clauses']:
 xs=by['TX2:240']['obligation']['caller_domain_obligations'];assert not any(q.get('id')==z['id']for q in xs);xs.append(z)
for r in ledger['rows']:r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
for n,key in [('SPECIFICATION','specification'),('TOP_COMPOSITION','top_composition'),('K086','K086'),('PROVENANCE','extraction_provenance')]:ledger['NNM_'+key]=J(E/('NNM_'+n+'.json'))
ledger['top_composition_obligations']=J(E/'NNM_TOP_COMPOSITION.json')['top_composition_obligations']
ledger.update(gate='INCOMPLETE_REFRESH_NO_PROMOTIONS',basis_gate='ledger28 PASS',basis='evidence/ledger28-20261111/NNL_LEDGER.json.xz',basis_delta='NNM_LEDGER_DELTA.json',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False,NNM_audit='NNM_AUDIT.json',NNM_missing='NNM_MISSING_RAW_ROOTS.json')
assert ledger['counts']==basis['counts'];assert all(r['status']==old['status']and r['canonical_callees']==old['canonical_callees']for r,old in zip(ledger['rows'],basis['rows']))
put('LEDGER',ledger,True)
put('LEDGER_DELTA',dict(basis=ledger['basis'],basis_uncompressed_sha256=(P/'NNL_LEDGER.json.sha256').read_text().strip(),before=dict(CLOSED=589,QUALIFIED=0,OPEN=10),after=dict(CLOSED=589,QUALIFIED=0,OPEN=10),new_closed_rows=[],new_count=0,gate='INCOMPLETE_NO_PROMOTIONS',missing_raw_roots=len(missing),missing_manifest='NNM_MISSING_RAW_ROOTS.json',candidates=[dict(row=c['row'],root=c['theorem'],status='OPEN',raw_pass=c['current_raw_result']is not None,exact_blocker=c['exact_blocker'])for c in review['candidates']],added_edges=[],removed_edges=[],trust_inventory_additions=[],trust_inventory_removals=[],wrapper_trust_unused=['ReviewedTranscription-TX1:344','ReviewedTranscription-TX2:240'],security_target_established=False))
print(json.dumps(dict(gate='INCOMPLETE',completed=len(results),required=len(required['roots']),missing=len(missing),counts=ledger['counts'],candidate_raw_passes=[c['row']for c in review['candidates']if c['current_raw_result']is not None])))
