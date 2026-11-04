"""Independent artifact checks and mutations; no prover or baseline replay."""
from pathlib import Path
import sys,json,lzma,hashlib,copy,re,collections,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
sys.path.insert(0,str(E));import NFX_ledger as ledger
J=lambda n:json.loads((E/n).read_text());D=ledger.read('evidence/ledger7-20261104/NFX_LEDGER.json');B=ledger.read('evidence/ledger6-20261104/NFK_LEDGER.json');BY={r['row']:r for r in B['rows']}
AE={'TX1:089','TX2:059','TX1:088','TX2:058'};AD={'TX1:105','TX2:071','TX1:104','TX2:070'}
DIRECT={r['row'] for r in J('NFX_COHERENCE_DENIALS.json')};std={'propext','Classical.choice','Quot.sound'}
def need(v,m):
 if not v:raise ValueError(m)
def check(d,routes,trust,audit):
 rows=d['rows'];need(len(rows)==587 and len({r['row'] for r in rows})==587,'inventory duplicate/count')
 need({r['row'] for r in rows}==set(BY),'inventory omission/addition')
 for r in rows:
  b=BY[r['row']];need((r['function'],r['frozen_body_sha256'])==(b['function'],b['frozen_body_sha256']),'frozen identity drift')
  need(r['composed_status'] in ['CLOSED','QUALIFIED','OPEN'],'invented status')
  if r['row'] in DIRECT:need(r['composed_status']=='QUALIFIED','legacy packet promoted')
  if r['row'] in AE:need(r['NFX_route']=='(ae)' and r['composed_status']=='CLOSED','ae route lost')
  if r['row'] in AD:need(r['NFX_route']=='(ad)' and r['composed_status']=='CLOSED','ad route lost')
  if r['composed_status']=='CLOSED':
   need(not r['open_transitive_dependencies'],'open transitive dependency')
   need(all(h['discharged_by'] for h in r['named_hypotheses']),'undischarged hypothesis')
   need(all(o['status']=='CLOSED' and o['discharged_by'] for o in r['caller_domain_obligations']),'open domain obligation')
  need(routes[r['row']]['status']==r['composed_status'] and routes[r['row']]['route']==r['NFX_route'],'route reconciliation')
 need(d['coverage']==dict(all_rows=d['NFX_coverage'],**d['NFX_per_tx']),'generic coverage stale')
 need(ledger.counts(rows)==d['NFX_coverage']==dict(total=587,CLOSED=167,QUALIFIED=89,OPEN=331,CLOSED_under_ae=4),'coverage mismatch')
 need(d['NFX_slices']['Q']['roots_CLOSED']==2 and d['NFX_slices']['S']['roots_CLOSED']==0 and d['NFX_slices']['D']['roots_CLOSED']==0,'root status inflation')
 need(d['NFX_inventory_defects']==['TX2:046','TX2:211'],'inventory defects hidden')
 need(not d['NFX_security_target_established'] and not d['NFX_cold_release_replay'],'unsupported release claim')
 tr={r['id']:r for r in trust['rows']}
 for n in ['RuntimeReturnData','RuntimeMemcmp','RuntimePersistence','NativeContractSemanticTransport']:need(tr[n]['status']=='ACCEPTED retained trust','trust pending/removed')
 need('1 <= |b| <= 1024' in tr['RuntimeReturnData']['scope'] and 'Empty replies excluded' in tr['RuntimeReturnData']['scope'],'return-data scope widened')
 for t in tr.values():need(t['direct_closed_rows']==[r['row'] for r in rows if r['composed_status']=='CLOSED' and t['id'] in r['NFX_trust_rows']],'trust use reconciliation')
 manifest=J('NFX_AUDIT_ROOTS.json');need(audit['root_count']==len(manifest['roots'])==263,'raw root omission')
 need({r['root'] for r in audit['results']}==set(manifest['roots']) and len(audit['results'])==263,'root multiset mismatch')
 for r in audit['results']:need(set(r['walked_axioms'])<=std,'nonstandard raw axiom')
 ledger.prior.fixtures(audit['fixtures'])
 need(audit['raw_walk_authoritative'] and audit['walker_byte_identical'] and audit['NEP_raw_action_byte_identical'],'audit implementation drift')
 need(all(audit['scan'][k]==0 for k in ['dangling','duplicate_owners','import_mismatches']),'coherence failure')
 need(audit['legacy_forest']['admitted'] is False and audit['legacy_forest']['all_forbidden_packet_owners_absent'],'legacy forest admission')
 need(audit['legacy_forest']['qualified_direct_rows']==85,'legacy denial omitted')
 return True
routes=J('NFX_ROUTES.json');trust=J('NFX_TRUST_USED.json');audit=J('NFX_AUDIT.json');check(D,routes,trust,audit)
mutations=[]
def reject(name,change,component='ledger'):
 d,t,r,a=D,trust,routes,audit
 if component=='ledger':d=copy.deepcopy(D);change(d)
 if component=='trust':t=copy.deepcopy(trust);change(t)
 if component=='audit':a=copy.deepcopy(audit);change(a)
 try:check(d,r,t,a)
 except (ValueError,AssertionError,KeyError):mutations.append(name)
 else:raise AssertionError('mutation admitted '+name)
reject('duplicate occurrence',lambda d:d['rows'].append(d['rows'][0]))
reject('frozen body identity',lambda d:d['rows'][0].update(frozen_body_sha256='0'*64))
reject('legacy row promotion',lambda d:next(r for r in d['rows'] if r['row'] in DIRECT).update(composed_status='CLOSED'))
reject('ae route omitted',lambda d:next(r for r in d['rows'] if r['row'] in AE).update(NFX_route='(y) plain'))
reject('ad route omitted',lambda d:next(r for r in d['rows'] if r['row'] in AD).update(NFX_route='(y) plain'))
reject('open caller domain',lambda d:next(r for r in d['rows'] if r['composed_status']=='CLOSED' and r['caller_domain_obligations'])['caller_domain_obligations'][0].update(status='OPEN'))
reject('undischarged hypothesis',lambda d:next(r for r in d['rows'] if r['composed_status']=='CLOSED' and r['named_hypotheses'])['named_hypotheses'][0].update(discharged_by=None))
reject('inventory defects erased',lambda d:d.update(NFX_inventory_defects=[]))
reject('headline claim',lambda d:d.update(NFX_security_target_established=True))
reject('return-data trust pending',lambda t:next(r for r in t['rows'] if r['id']=='RuntimeReturnData').update(status='PENDING'),'trust')
reject('empty return data admitted',lambda t:next(r for r in t['rows'] if r['id']=='RuntimeReturnData').update(scope='all replies including empty'),'trust')
reject('nonstandard raw axiom',lambda a:a['results'][0]['walked_axioms'].append('sorryAx'),'audit')
reject('raw root omitted',lambda a:a['results'].pop(),'audit')
for k in ['dangling','duplicate_owners','import_mismatches']:reject(k,lambda a,k=k:a['scan'].update({k:1}),'audit')
reject('legacy forest admitted',lambda a:a['legacy_forest'].update(admitted=True),'audit')
reject('planted negative fixture omitted',lambda a:a['fixtures'].pop(),'audit')
# Exact fresh child observation, not an archived status line accidentally read
# after predecessor report redirection. Both must agree before any admission.
fresh=(E/'NFX_replay_outputs/NEZ/evidence/ledger5-20261104/NEZ_NEI_STATUS.log').read_text().splitlines()[-1]
old=(R/'evidence/ledger5-20261104/NEZ_NEI_STATUS.log').read_text().splitlines()[-1]
need(json.loads(fresh)==json.loads(old),'fresh isolated NEI status differs from historical result')
for n in ['NEN','NEZ','NFK','NET','NFE','NFS','NFJ','NFQ']:need(J('NFX_REPLAY_'+n+'.json')['exit_status']==0,'predecessor replay failed '+n)
# One immutable report/manifest inputs corpus; source-only report repair is visible.
source=(E/'NFX_COMBINED_IMPORT.lean').read_text();need(set(re.findall(r'^#print axioms (\S+)',source,re.M))==set(J('NFX_AUDIT_ROOTS.json')['roots']),'combined manifest drift')
need(hashlib.sha256(source.encode()).hexdigest()==audit['combined_source_sha256'],'combined source pin')
loaded=list(map(json.loads,(E/'NFX_LOADED_scan.jsonl').read_text().splitlines()));need(len(loaded)==13126 and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in loaded),'loaded scan not clean')
need(not(subprocess.check_output(['git','diff','--name-only','--','crates','programs'],cwd=R)),'shipped source changed')
slots=[json.loads(l) for l in (E/'NFX_ATTEMPTS.jsonl').read_text().splitlines() if re.fullmatch(r'NFX_L\d{3}',json.loads(l).get('attempt',''))]
need(len(slots)==40 and {r['attempt'] for r in slots}=={f'NFX_L{i:03}' for i in range(1,41)},'40-slot budget mismatch')
need(all(p.stat().st_size<=20_000_000 for p in E.rglob('*') if p.is_file()),'oversized evidence')
print(json.dumps(dict(status='PASS',mutations_rejected=mutations,coverage=D['NFX_coverage'],host_slots_used=40,kani=0,extraction=0,source_statement_audits=['NFX_L036','NFX_L037','NFX_L038','NFX_L039','NFX_L040'])))
