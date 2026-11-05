"""Ledger refresh: unchanged 599-row graph; only validator-admitted status updates."""
from pathlib import Path
import json,lzma,hashlib,collections,copy,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):
 p=Path(p);p=p if p.is_absolute()else R/p
 if p.exists():return json.loads(p.read_bytes())
 raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(raw)==Path(str(p)+'.sha256').read_text().strip();return json.loads(raw)
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if len(raw)>20_000_000:
  Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(H(raw)+'\n')
 else:p.write_bytes(raw)
def counts(rs):return dict(total=len(rs),**{s:sum(r['composed_status']==s for r in rs)for s in ['CLOSED','QUALIFIED','OPEN']})
def closure(g,roots):
 seen={f:[f]for f in roots};q=collections.deque(roots)
 while q:
  f=q.popleft()
  for c in sorted(g.get(f,[])):
   if c in g and c not in seen:seen[c]=seen[f]+[c];q.append(c)
 return seen
def ids(x):
 for k in ['new_closed_rows','newly_closed','new_rows','changed_rows']:
  if isinstance(x.get(k),list):return x[k]
 raise ValueError('No explicit row list')
def build():
 out=J('evidence/ledger10-20261106/NHO_LEDGER.json');before=copy.deepcopy(out);by={r['row']:r for r in out['rows']};assert len(by)==599 and counts(out['rows'])==dict(total=599,CLOSED=335,QUALIFIED=0,OPEN=264)
 delta=[];overlap=[];validatorpins=[]
 for a in ['NHK','NHN','NHG','NHS','NHM','NHJ','NHX','NHU']:
  rc=J(E/('NII_REPLAY_'+a+'.json'));assert rc['exit_status']==0,a
  d=next((R/'evidence').glob('*/'+a+'_HANDOFF.md')).parent;p=d/(a+'_LEDGER_DELTA.json');x=J(p);rows=ids(x)
  mirror=E/'NII_replay_outputs'/p.relative_to(R)
  if mirror.exists():assert set(rows)==set(ids(J(mirror))),(a,'regenerated row set changed')
  cp=d/(a+'_CLOSED.json');cert=J(cp);fs=cert.get('functions',[cert]);new=[]
  for rid in rows:
   r=by[rid]
   if a=='NHK':f=cert;assert f['row']==rid
   elif a=='NHJ':
    choices=[f for f in fs if f['subject']==r['function']];assert choices
    f=choices[0] if len(choices)==1 else next(f for f in choices if f['id']==('NHJ::distinct3'if r['transaction']=='TX1'else'NHJ::distinct7'))
    dr=next(v for v in x['rows']if v['row']==rid);assert dr['composed_status']=='CLOSED' and dr['function']==r['function'] and not dr['open_transitive_dependencies']
   else:f=next(f for f in fs if rid in f.get('rows',[]))
   assert f.get('function',f.get('subject'))==r['function'],(a,rid)
   assert not f.get('inner_hypotheses_remaining',[])
   if f.get('frozen_body_sha256'):assert r['frozen_body_sha256']==f['frozen_body_sha256']
   if r['composed_status']=='CLOSED':overlap.append(dict(row=rid,provider=a,existing=r.get('NHO_provider')));continue
   assert r['composed_status']=='OPEN'
   route='(ah)'if a=='NHK'else'(al)'if a=='NHN'and rid=='TX1:006'else'(ai)'if a=='NHS'else'(ak)'if a=='NHJ'else'(ae)'if a=='NHU'and rid=='TX1:322'else'(y)'
   r.update(composed_status='CLOSED',NII_provider=a,NII_route=route,NII_certificate=dict(path=str(cp.relative_to(R)),sha256=H(cp.read_bytes()),delta=str(p.relative_to(R)),validator=rc['result']['unchanged_validator'],packet=f),NII_selected_roots=[f[k]for k in ['lean_root','model_root','outcome_root','model_theorem','export']if isinstance(f.get(k),str)])
   new.append(rid)
  delta.append(dict(prefix=a,path=str(p.relative_to(R)),sha256=H(p.read_bytes()),claimed_rows=rows,new_closed_rows=new,validator_receipt='NII_REPLAY_'+a+'.json',checks_removed=0))
  vp=R/rc['result']['unchanged_validator'];validatorpins.append(dict(path=str(vp.relative_to(R)),sha256=H(vp.read_bytes()),unchanged=True,nested=rc.get('nested_validators',[])))
 for r in out['rows']:
  r.setdefault('NII_provider',r.get('NHO_provider'));r.setdefault('NII_route',r.get('NHO_route'));r['NII_trust_used']=r.get('NHO_trust_used',[]).copy()
  if r['composed_status']=='CLOSED':r['NII_trust_used']=sorted(set(r['NII_trust_used'])|{'NativeContractSemanticTransport'})
  if r['row']=='TX1:168':r['NII_trust_used']=sorted(set(r['NII_trust_used'])|{'ReviewedTranscription-queries_from_pairs'})
  if r['row']in ['TX1:036','TX1:040','TX1:041','TX1:043','TX1:044']:assert r['composed_status']=='OPEN';r['NII_boundary']='TOOL-BOUNDARY'
 for old,new in zip(before['rows'],out['rows']):
  assert all(old[k]==new[k]for k in ['row','canonical_callees','frozen_body_sha256','function','transaction'])
 coverage=counts(out['rows']);assert coverage==dict(total=599,CLOSED=393,QUALIFIED=0,OPEN=206),coverage
 spec=J('docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices'];g=collections.defaultdict(set)
 for r in out['rows']:g[r['function']].update(r['canonical_callees'])
 S=set(closure(g,spec['S']['roots']));Q=set(closure(g,spec['Q']['roots']));D=set(closure(g,['programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction']))-S-Q
 tx={t:counts([r for r in out['rows']if r['transaction']==t])for t in ['TX1','TX2']};slices={s:counts([r for r in out['rows']if r['function']in fs])for s,fs in [('S',S),('Q',Q),('D',D)]}
 trust=copy.deepcopy(out['trust_rows']);tby={t['id']:t for t in trust}
 additions=[dict(id='ReviewedTranscription-queries_from_pairs',status='ADDED-LEAD',ruling='(ah)',domain='NHK_word_ref reviewed transcription of frozen queries_from_pairs; not an extraction proof',used=True),dict(id='RuntimeReturnDataClear',status='ADDED-LEAD',ruling='(am)',domain='Empty set_return_data in same instruction clears observable return data until later set; no failure/cross-instruction guarantee',used=False)]
 for t in additions:
  assert t['id']not in tby;trust.append(t);tby[t['id']]=t
 for t in trust:
  t['direct_closed_rows']=[r['row']for r in out['rows']if r['composed_status']=='CLOSED'and t['id']in r['NII_trust_used']]
  if t['id']=='RuntimeCpiReadonlyEntry7':assert not t.get('used')and not t['direct_closed_rows']
 tby['RuntimeClockSlotBinding']['use_sites']=['same-instruction bankSlot binding at pending entry/adapter instantiation; no direct newly CLOSED row']
 tby['RuntimeReturnDataClear']['use_sites']=['NHJ/NHD stage2 return-register clear source-realization obligation; no CLOSED full stage2 row; NIB register continuity producer remains OPEN']
 tby['ReviewedTranscription-prepared_claim']['use_sites']=['TX1:193 NGY packet','TX1:179 NHS constructor callee composition','TX1:186 NHS checkpoint composition']
 tby['ReviewedTranscription-queries_from_pairs']['use_sites']=['TX1:168 NHK packet','TRANSCRIPT.actual_queries AspisR1.NGP_TRANSCRIPT.actual_queries','TX1:179/186 NHS composition']
 pool=copy.deepcopy(out['NHO_pool_consumer_rows']);pr=J(E/'NII_REPLAY_NHP.json');assert pr['exit_status']==0
 px=J('evidence/pool-b3-20261106/NHP_LEDGER_DELTA.json');assert len(px['rows'])==2 and all(r['composed_status']=='CLOSED'for r in px['rows']);pool+=px['rows']
 for a in ['NHW','NHZ','NIB','NIF','NHT','NHV','NIA','NIC']:
  d=next((R/'evidence').glob('*/'+a+'_HANDOFF.md')).parent;p=d/(a+'_LEDGER_DELTA.json');x=J(p)
  for key in ['newly_closed','row_promotions','ledger_mutations']:
   if key in x:assert not x[key],(a,key,'unexpected support-only promotion')
 out.update(coverage=dict(all_rows=coverage,**tx),NII_coverage=coverage,NII_per_tx=tx,NII_slices=slices,NII_deltas=delta,NII_headline='AspisR1.RPx_Deployed.deployed',NII_authority='NII fields and composed_status; NHO and prior fields are checkpoint history',NII_security_target_established=False,NII_cold_release_replay=False,NII_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),NII_pool_consumer_rows=pool,trust_rows=trust)
 put('NII_LEDGER.json',out);put('NII_ROUTES.json',{r['row']:dict(function=r['function'],status=r['composed_status'],provider=r['NII_provider'],route=r['NII_route'],boundary=r.get('NII_boundary'),trust_used=r['NII_trust_used'])for r in out['rows']})
 put('NII_TRUST_USED.json',dict(rows=trust,route_inventory=['(y)','(ad)','(ae)','(af)','(ah)','(ai)','(ak)','(al)','reclassification'],use_semantics='direct_closed_rows is explicit packet use; use_sites includes transitive composition and OPEN realization sites; zero direct use is never a discharge',Pool_A='(af) RECLASSIFICATION outside599',Pool_B='OPEN production association; three helpers CLOSED',Pool_D='PROVED-conditional model theorem; production continuation OPEN',source_realization_obligations=['NIB-P1 return-register continuity','NIB-P2 actual validation dictionary','NIB-P3 actual lane dictionary','NIB-P4 production settlement continuation','NHY_/NHD_ source/entry candidates; not adopted trust'],no_trust_removed=True))
 put('NII_COUNT_RECONCILIATION.json',dict(prior=before['NHO_coverage'],current=coverage,deltas=delta,overlaps=overlap,added=sum(len(d['new_closed_rows'])for d in delta),graph_changes=[],requested_count_reproduced=True))
 put('NII_VALIDATOR_PROVENANCE.json',validatorpins)
 lines=['# Ledger refresh 11','','**393 CLOSED / 0 QUALIFIED / 206 OPEN of 599. Target not yet established.**','','CLOSED means composed hybrid source/model credit on caller-established domains under retained trust; no headline premise is retired. The unchanged validators reproduce all58 additional occurrences, without overlap. NII_COUNT_RECONCILIATION.json pins exact row membership and provenance.','','| Scope | Total | CLOSED | QUALIFIED | OPEN |','|---|---:|---:|---:|---:|']
 for k,v in [('all',coverage),*tx.items(),*slices.items()]:lines.append('| '+k+' | '+' | '.join(str(v[z])for z in ['total','CLOSED','QUALIFIED','OPEN'])+' |')
 lines+=['','Routes: (y), (ad), (ae), (af), (ah), (ai), (ak), (al), and P6/D188 option-A reclassification. CM31::inv_with covers ONLY the deployed M31::inv instantiation under (al). TOOL-BOUNDARY TX1:036/040/041/043/044 remain OPEN.','','## Pool consumer (outside599)','','| Row | Status | Route |','|---|---|---|','| Pool A meta association | CLOSED by reclassification | (af) |']
 for r in pool:lines.append('| '+r['row']+' | CLOSED | '+r.get('route','(y)')+' |')
 lines+=['| POOL.prefix_to_cpi (B) | OPEN | production association |','| POOL.read_to_settlement (D) | PROVED-conditional model / OPEN production | NIB_ReadToSettlement.read_to_settlement |','','K086 remains an abort/liveness finding on a valid exclusive-borrow prestate; production reachability is UNPROVED. No trust added for this finding. RuntimeCpiReadonlyEntry7 PENDING/unused. NIB-P1/P2 and NHY_/NHD_ candidates remain source-realization obligations, never trust.','','## Verifier inventory','','| Row | Function | Status | Route / boundary | Provider |','|---|---|---|---|---|']
 lines+=['| '+r['row']+' | '+r['function']+' | '+r['composed_status']+' | '+str(r.get('NII_boundary')or r['NII_route']or'')+' | '+str(r['NII_provider'])+' |'for r in out['rows']]
 (E/'NII_LEDGER.md').write_text('\n'.join(lines)+'\n');print(json.dumps(dict(coverage=coverage,slices=slices,per_tx=tx)))
if __name__=='__main__':build()
