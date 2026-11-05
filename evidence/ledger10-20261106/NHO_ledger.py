"""Add validated deltas to the immutable NGZ 599-row canonical graph."""
from pathlib import Path
import json,lzma,hashlib,collections,subprocess,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):
 p=Path(p);p=p if p.is_absolute()else R/p
 if p.is_file():return json.loads(p.read_bytes())
 raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(raw)==Path(str(p)+'.sha256').read_text().strip();return json.loads(raw)
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if len(raw)>20_000_000:(E/(n+'.xz')).write_bytes(lzma.compress(raw,preset=6));(E/(n+'.sha256')).write_text(H(raw)+'\n')
 else:p.write_bytes(raw)
def closure(g,roots):
 seen={f:[f]for f in roots};q=collections.deque(roots)
 while q:
  f=q.popleft()
  for c in sorted(g.get(f,[])):
   if c in g and c not in seen:seen[c]=seen[f]+[c];q.append(c)
 return seen
def build():
 out=J('evidence/ledger9-20261105/NGZ_LEDGER.json');before=copy.deepcopy(out);by={r['row']:r for r in out['rows']};deltas=[];overlaps=[]
 assert len(by)==599 and out['NGZ_coverage']==dict(total=599,CLOSED=303,QUALIFIED=0,OPEN=296)
 for a in ['NGW','NGY','NGX','NHE','NHF','NHI','NHH']:
  receipt=J(E/('NHO_REPLAY_'+a+'.json'));assert receipt['exit_status']==0,a
  d=next((R/'evidence').glob('*/'+a+'_HANDOFF.md')).parent;p=d/(a+'_LEDGER_DELTA.json');x=J(p)
  ids=x.get('new_closed_rows',x.get('newly_closed',x.get('new_rows',[])))
  if isinstance(ids,int):ids=x['changed_rows']
  certpath=d/(a+'_CLOSED.json');cert=J(certpath);fs=cert.get('functions',[]);new=[]
  if a=='NGY':fs=[dict(cert,rows=cert['closed'])]
  if a=='NHF':fs=[dict(cert,rows=cert['rows'],function=cert['functions'][0],details=J(d/'NHF_CERTIFICATES.json'))]
  for rid in ids:
   r=by[rid];f=next(f for f in fs if rid in f.get('rows',[]));assert f['function']==r['function'],(a,rid)
   if r['composed_status']=='CLOSED':overlaps.append(dict(row=rid,provider=a,existing=r.get('NGZ_provider'),function=r['function']));continue
   assert r['composed_status']=='OPEN'
   assert not f.get('inner_hypotheses_remaining',[])
   if f.get('frozen_body_sha256'):assert f['frozen_body_sha256']==r['frozen_body_sha256']
   route='(ah)'if a=='NGY'or a=='NHE'and rid=='TX2:119'else'(y)/(ai)'if a=='NHF'else'(y)/(al)'if a=='NHH'and rid=='TX1:005'else'(y)'
   r.update(composed_status='CLOSED',NHO_provider=a,NHO_route=route,NHO_certificate=dict(path=str(certpath.relative_to(R)),sha256=H(certpath.read_bytes()),delta=str(p.relative_to(R)),validator=receipt['result']['unchanged_validator'],packet=f),NHO_selected_roots=[f[k]for k in ['lean_root','model_root','outcome_root']if isinstance(f.get(k),str)])
   new.append(rid)
  deltas.append(dict(prefix=a,path=str(p.relative_to(R)),sha256=H(p.read_bytes()),claimed_rows=ids,new_closed_rows=new,validator_receipt='NHO_REPLAY_'+a+'.json',checks_removed=0))
 for r in out['rows']:
  r.setdefault('NHO_provider',r.get('NGZ_provider'));r.setdefault('NHO_route',r.get('NGZ_route'));r['NHO_trust_used']=r.get('NGZ_trust_used',[])
  if r['composed_status']=='CLOSED':r['NHO_trust_used']=sorted(set(r['NHO_trust_used'])|{'NativeContractSemanticTransport'})
  if r['row']=='TX1:193':r['NHO_trust_used']=sorted(set(r['NHO_trust_used'])|{'ReviewedTranscription-prepared_claim'})
  if r['row']in ['TX1:036','TX1:040','TX1:041','TX1:043','TX1:044']:assert r['composed_status']=='OPEN';r['NHO_boundary']='TOOL-BOUNDARY'
 def counts(rs):return dict(total=len(rs),**{s:sum(r['composed_status']==s for r in rs)for s in ['CLOSED','QUALIFIED','OPEN']})
 coverage=counts(out['rows']);assert coverage==dict(total=599,CLOSED=335,QUALIFIED=0,OPEN=264)
 sets=J('evidence/ledger9-20261105/NGZ_SLICES.json');g=collections.defaultdict(set)
 for r in out['rows']:g[r['function']].update(r['canonical_callees'])
 spec=J('docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices'];S=set(closure(g,spec['S']['roots']));Q=set(closure(g,spec['Q']['roots']));D=set(closure(g,['programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction']))-S-Q
 assert all(set(sets[s])==v for s,v in [('S',S),('Q',Q),('D',D)])
 slices={s:counts([r for r in out['rows']if r['function']in fs])for s,fs in [('S',S),('Q',Q),('D',D)]};tx={t:counts([r for r in out['rows']if r['transaction']==t])for t in ['TX1','TX2']}
 for old,r in zip(before['rows'],out['rows']):assert old['row']==r['row']and old['canonical_callees']==r['canonical_callees']and old['frozen_body_sha256']==r['frozen_body_sha256']
 trust=out['trust_rows'];trust.append(dict(id='ReviewedTranscription-prepared_claim',status='ADDED-LEAD',ruling='(ah)',domain='reviewed hand transcription f_ref/f_ref5 in NGY prepared_claim packet; explicit P6/D188 trust, not extraction proof',used=True))
 for t in trust:
  t['direct_closed_rows']=[r['row']for r in out['rows']if r['composed_status']=='CLOSED'and t['id']in r['NHO_trust_used']]
  if t['id']=='RuntimeCpiReadonlyEntry7':assert not t.get('used')and not t['direct_closed_rows']
 # NGW old final scanner exit 1 cannot alone earn credit; NHE independently reran the unchanged scan.
 rerun=J('evidence/slice-d-finish3-20261106/NHE_L001/receipt.json');assert rerun['exit_status']==0
 pool=J('evidence/pool-leaves-20261105/NHC_LEDGER_DELTA.json');assert J(E/'NHO_REPLAY_NHC.json')['exit_status']==0
 pool_rows=pool['rows'];assert len(pool_rows)==1 and pool_rows[0]['status']=='CLOSED'
 out.update(coverage=dict(all_rows=coverage,**tx),NHO_coverage=coverage,NHO_per_tx=tx,NHO_slices=slices,NHO_deltas=deltas,NHO_headline='AspisR1.RPx_Deployed.deployed',NHO_authority='NHO fields and composed_status; NGZ and earlier fields are checkpoint history',NHO_security_target_established=False,NHO_cold_release_replay=False,NHO_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),NHO_pool_consumer_rows=pool_rows)
 put('NHO_LEDGER.json',out);put('NHO_ROUTES.json',{r['row']:dict(function=r['function'],status=r['composed_status'],provider=r['NHO_provider'],route=r['NHO_route'],boundary=r.get('NHO_boundary'),trust_used=r['NHO_trust_used'])for r in out['rows']});put('NHO_TRUST_USED.json',dict(rows=trust,use_semantics='direct_closed_rows means explicit certificate use; zero direct use is never discharge of retained realization',route_inventory=['(y)','(ad)','(ae)','(af)','(ah)','(ai)','(al)','reclassification'],reviewed_transcription_ah_uses=['TX1:193'],Pool_A='(af) reclassification outside599',Pool_B_D='OPEN; supported_loader helper CLOSED (y)',no_trust_removed=True));put('NHO_COUNT_RECONCILIATION.json',dict(prior=before['NGZ_coverage'],current=coverage,deltas=deltas,already_closed_overlaps=overlaps,requested_estimate=dict(CLOSED=325,OPEN=274),difference='32 new occurrences: 34 claimed minus NGX TX1:151/152 already CLOSED; estimate differs by ten',graph_changes=[],NGW_scanner_credit='NHE_L001 exit0 rerun required and checked'))
 lines=['# Ledger refresh 10','','Target not yet established. CLOSED means conditional hybrid composition under retained trust.','','| Scope | Total | CLOSED | QUALIFIED | OPEN |','|---|---:|---:|---:|---:|']
 for n,v in [('all',coverage),*tx.items(),*slices.items()]:lines.append('| '+n+' | '+' | '.join(str(v[k])for k in ['total','CLOSED','QUALIFIED','OPEN'])+' |')
 lines+=['','The supplied deltas reproduce 335/599 CLOSED, ten above the approximate request estimate. 34 claimed occurrences minus two already CLOSED NGX overlaps produce32 new rows. NHO_COUNT_RECONCILIATION.json retains exact membership; no graph or source change. NGW credit requires NHE_L001 scanner rerun exit0.','', 'Routes are explicit per row: (y), (ad), (ae), (ah), (ai), (al), and reclassification. Pool A uses (af), outside599. NHH CM31::inv is a fixed M31::inv specialization; generic CM31::inv_with remains OPEN under the K-2 quarantine. TOOL-BOUNDARY TX1:036/040/041/043/044 remain OPEN.','', 'RuntimeClockSlotBinding and ReviewedTranscription-prepared_claim are ADDED-LEAD, the latter used by TX1:193 under (ah). RuntimeCpiReadonlyEntry7 is ADDED-PENDING-LEAD and UNUSED. RuntimeReturnData (nonempty1..1024) and RuntimeMemcmp remain ACCEPTED. P6/D188 option A is reclassification, never removal. L154 is a statement parameter; coherent digest/error op43/op44.','','## Pool consumer rows (outside599)','','| Row | Status | Route |','|---|---|---|','| Pool meta association A | CLOSED by reclassification | (af) |','| '+pool_rows[0]['row']+' | CLOSED | (y) |','| POOL.prefix_to_cpi (B) | OPEN | native production association |','| POOL.read_to_settlement (D) | OPEN | same-CPI settlement |','','## Verifier inventory','','| Row | Function | Status | Route/boundary | Provider |','|---|---|---|---|---|']
 lines+=['| '+r['row']+' | '+r['function']+' | '+r['composed_status']+' | '+str(r.get('NHO_boundary')or r['NHO_route']or'')+' | '+str(r['NHO_provider'])+' |'for r in out['rows']]
 (E/'NHO_LEDGER.md').write_text('\n'.join(lines)+'\n');print(json.dumps(dict(coverage=coverage,slices=slices,per_tx=tx)))
if __name__=='__main__':build()
