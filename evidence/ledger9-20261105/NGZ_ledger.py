"""Refresh by validated additive deltas; retain the reviewed NGB producer graph."""
from pathlib import Path
import ast,json,lzma,hashlib,copy,collections,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def J(p):
 p=R/p
 if p.exists():return json.loads(p.read_text())
 raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert sha(raw)==Path(str(p)+'.sha256').read_text().strip();return json.loads(raw)
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if len(raw)>20000000:(E/(n+'.xz')).write_bytes(lzma.compress(raw));(E/(n+'.sha256')).write_text(sha(raw)+'\n')
 else:p.write_bytes(raw)
def closure(g,roots):
 seen={f:[f] for f in roots};q=collections.deque(roots)
 while q:
  f=q.popleft()
  for c in sorted(g[f]):
   if c in g and c not in seen:seen[c]=seen[f]+[c];q.append(c)
 return seen
# Reuse unchanged reviewed overlay producer and compiler/source corroboration.
s=(R/'evidence/ledger8-20261105/NGJ_ledger.py').read_text();tree=ast.parse(s)
f=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='inventory')
code=ast.unparse(f).replace('NGJ_','NGZ_');exec(compile(code,'NGZ_inventory','exec'))
def build():
 out=J('evidence/ledger8-20261105/NGJ_LEDGER.json');graph=inventory()
 assert [(r['row'],r['canonical_callees'])for r in graph['rows']]==[(r['row'],r['canonical_callees'])for r in out['rows']]
 before=copy.deepcopy(out);by={r['row']:r for r in out['rows']};deltas=[]
 for a in ['NGH','NGD','NFW','NGC','NGO','NGM','NGT','NGV','NGN','NGU','NGK','NGA','NGG']:
  receipt=J('evidence/ledger9-20261105/NGZ_REPLAY_'+a+'.json');assert receipt['exit_status']==0,a
  d=next((R/'evidence').glob('*/'+a+'_HANDOFF.md')).parent;p=d/(a+'_LEDGER_DELTA.json');x=J(p)
  ids=x.get('new_closed_rows',x.get('newly_closed',[r['row']for r in x.get('updates',[]) if r['to_status']=='CLOSED']))
  # The validator-generated delta must retain the exact admitted row set.
  replay=E/'NGZ_replay_outputs'/p.relative_to(R)
  if replay.exists():
   rx=json.loads(replay.read_text());rids=rx.get('new_closed_rows',rx.get('newly_closed',[r['row']for r in rx.get('updates',[]) if r['to_status']=='CLOSED']))
   assert set(ids)==set(rids),(a,ids,rids)
  certpath=d/(a+'_CLOSED.json');cert=J(certpath) if certpath.exists()else x
  rr=x.get('rows',x.get('updates',[]));functions={r['row']:r['function'] for r in rr if 'row'in r and 'function'in r}
  for c in cert.get('functions',[]):
   for rid in c.get('rows',[]):functions[rid]=c['function']
  ledger=d/(a+'_COMPOSED_LEDGER.json');cb={r['row']:r for r in J(ledger)['rows']}if ledger.exists()or Path(str(ledger)+'.xz').exists()else {}
  for rid in ids:
   r=by[rid];assert r['composed_status']=='OPEN',(a,rid)
   assert functions.get(rid,cb.get(rid,{}).get('function'))==r['function'],(a,rid)
   oldgraph=r['canonical_callees']
   if rid in cb:
    assert cb[rid]['frozen_body_sha256']==r['frozen_body_sha256'];r.update(copy.deepcopy(cb[rid]));r['canonical_callees']=oldgraph
   for c in rr:
    if c.get('row')==rid and c.get('frozen_body_sha256'):assert c['frozen_body_sha256']==r['frozen_body_sha256']
   r.update(composed_status='CLOSED',NGZ_provider=a,NGZ_route='(y)/(ai)'if a=='NGT'else'(y)',NGZ_certificate=dict(path=str(certpath.relative_to(R)),sha256=sha(certpath.read_bytes()),validated_delta=str(p.relative_to(R)),validator=receipt['result']['unchanged_validator'],details=cert))
  deltas.append(dict(prefix=a,path=str(p.relative_to(R)),sha256=sha(p.read_bytes()),new_closed_rows=ids,validator_receipt='NGZ_REPLAY_'+a+'.json'))
 for r in out['rows']:
  r.setdefault('NGZ_provider',r.get('NGJ_provider'));r.setdefault('NGZ_route',r.get('NGJ_route'))
  r['NGZ_trust_used']=r.get('NGJ_trust_used',[])
  if r['composed_status']=='CLOSED':r['NGZ_trust_used']=sorted(set(r['NGZ_trust_used'])|{'NativeContractSemanticTransport'})
  if r['row']in ['TX1:036','TX1:040','TX1:041','TX1:043','TX1:044']:r['NGZ_boundary']='TOOL-BOUNDARY';assert r['composed_status']=='OPEN'
 # No selected claim may be admitted solely through an OPEN row.
 accepted={c for r in out['rows']if r['composed_status']=='CLOSED'for c in r.get('selected_claims',[])}
 denied={c for r in out['rows']if r['composed_status']!='CLOSED'for c in r.get('selected_claims',[])}-accepted
 for r in out['rows']:
  bad=[c for o in r.get('caller_domain_obligations',[])for c in o.get('callee_claims',[])if c in denied]
  if r['composed_status']=='CLOSED'and bad:r.update(composed_status='QUALIFIED',NGZ_denial=bad)
 def counts(rs):return dict(total=len(rs),**{s:sum(r['composed_status']==s for r in rs)for s in ['CLOSED','QUALIFIED','OPEN']})
 g=collections.defaultdict(set)
 for r in out['rows']:g[r['function']].update(r['canonical_callees'])
 spec=J('docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices'];root='programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction'
 sets={s:set(closure(g,spec[s]['roots']))for s in ['S','Q']};sets['D']=set(closure(g,[root]))-sets['S']-sets['Q']
 slices={s:counts([r for r in out['rows']if r['function']in fs])for s,fs in sets.items()}
 oldsets=J('evidence/ledger8-20261105/NGJ_SLICES.json');assert all(set(oldsets[s])==sets[s]for s in sets)
 trust=out['trust_rows'];existing={r['id']for r in trust}
 for id,status,domain in [('RuntimeClockSlotBinding','ADDED-LEAD','clockGet ctx = ok v implies v = bankSlot ctx on same instruction context; no monotonicity/epoch/success claim'),('RuntimeCpiReadonlyEntry7','ADDED-PENDING-LEAD','UNUSED; pending CPI proposal, not admitted')]:
  if id not in existing:trust.append(dict(id=id,status=status,domain=domain,direct_closed_rows=[],plan_uses=['NGP_L159 physical_instance (OPEN)']if id=='RuntimeClockSlotBinding'else[],used=False))
 for t in trust:
  t['direct_closed_rows']=[r['row']for r in out['rows']if r['composed_status']=='CLOSED'and t['id']in r['NGZ_trust_used']]
  if t['id']=='RuntimeSha256Value':
   t['retained_value_realization_uses']=['TX1:327','TX2:210'];t['note']='NGC forwarding proves exact syscall slices and unchanged full reply only; SHA256=H is retained runtime realization, not a native arithmetic proof.'
 coverage=counts(out['rows']);tx={t:counts([r for r in out['rows']if r['transaction']==t])for t in ['TX1','TX2']}
 out.update(coverage=dict(all_rows=coverage,**tx),NGZ_coverage=coverage,NGZ_per_tx=tx,NGZ_slices=slices,NGZ_deltas=deltas,NGZ_headline='AspisR1.RPx_Deployed.deployed',NGZ_authority='NGZ fields and composed_status; earlier fields are retained checkpoint history',NGZ_security_target_established=False,NGZ_cold_release_replay=False,NGZ_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip())
 put('NGZ_LEDGER.json',out);put('NGZ_SLICES.json',{s:sorted(v)for s,v in sets.items()});put('NGZ_ROUTES.json',{r['row']:dict(function=r['function'],status=r['composed_status'],provider=r['NGZ_provider'],route=r['NGZ_route'],boundary=r.get('NGZ_boundary'),trust_used=r['NGZ_trust_used'])for r in out['rows']});put('NGZ_TRUST_USED.json',dict(rows=trust,use_semantics='direct_closed_rows records explicit local certificate use; retained_root_context remains separately conditional for all rows; zero direct use never means discharged',route_inventory=['(y)','(ad)','(ae)','(af)','(ah)','(ai)','reclassification'],reviewed_transcription_ah_uses=[],Pool_A='(af) reclassification outside verifier inventory; B/D OPEN',no_trust_removed=True));put('NGZ_COUNT_RECONCILIATION.json',dict(prior=before['NGJ_coverage'],current=coverage,deltas=deltas,slices=slices,count_change=coverage['CLOSED']-before['NGJ_coverage']['CLOSED'],membership_changes=[],C0032='ADMITTED through unchanged NGB producer, no new row, existing TX1:310'))
 lines=['# Ledger refresh 9','','Target not yet established. CLOSED means conditional hybrid composition under retained trust, not deployed soundness.','','| Scope | Total | CLOSED | QUALIFIED | OPEN |','|---|---:|---:|---:|---:|']
 for n,v in [('all',coverage),*tx.items(),*slices.items()]:lines.append('| '+n+' | '+' | '.join(str(v[k])for k in ['total','CLOSED','QUALIFIED','OPEN'])+' |')
 lines+=['','NGB 599-row basis; C0032 admitted through the unchanged reviewed overlay producer and LEAD_B007 MIR. No count or slice membership change. Four S/Q overlap occurrences count once globally. Pool has no consumer row in this inventory; B/D remain OPEN.','', 'Routes (y), (ad), (ae), (ai) and reclassification are explicit per occurrence. Pool A uses (af). No (ah) certificate is admitted; five field helper rows remain TOOL-BOUNDARY. Native contract semantic transport remains P6/D188 option-A reclassification, never removal. RuntimeClockSlotBinding is ADDED-LEAD; RuntimeCpiReadonlyEntry7 is ADDED-PENDING-LEAD and unused. RuntimeReturnData nonempty1..1024 and RuntimeMemcmp remain ACCEPTED. L154 is a statement parameter; coherent digest/error slots are op43/op44.','','| Row | Function | Status | Route/boundary | Provider |','|---|---|---|---|---|']
 lines+=['| '+r['row']+' | '+r['function']+' | '+r['composed_status']+' | '+str(r.get('NGZ_boundary')or r['NGZ_route']or'')+' | '+str(r['NGZ_provider'])+' |'for r in out['rows']]
 (E/'NGZ_LEDGER.md').write_text('\n'.join(lines)+'\n');print(json.dumps(dict(coverage=coverage,slices=slices)))
if __name__=='__main__':build()
