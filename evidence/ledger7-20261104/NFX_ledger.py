"""Additive NDT ledger admission; every promotion is backed by replayed gates.

No prover launches. Inherited fields remain historical; NFX_* governs refresh7.
All changes to occurrence identity, denial checks or certificate domains fail.
"""
from pathlib import Path
import json,lzma,copy,hashlib,collections,subprocess,sys,re
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
sys.path.insert(0,str(R/'evidence/ledger6-20261104'));import NFK_validate as prior
J=lambda p:json.loads((R/p).read_text())
def read(p):
 p=R/p
 if p.exists():return json.loads(p.read_text())
 raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==Path(str(p)+'.sha256').read_text().strip();return json.loads(raw)
def pin(path):
 p=R/path;raw=p.read_bytes();committed=subprocess.check_output(['git','show','HEAD:'+path],cwd=R);assert raw==committed,'dirty evidence '+path
 return dict(path=path,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
def need(ok,msg):
 if not ok:raise ValueError(msg)
def counts(rows):
 c=collections.Counter(r['composed_status'] for r in rows);return dict(total=len(rows),CLOSED=c['CLOSED'],QUALIFIED=c['QUALIFIED'],OPEN=c['OPEN'],CLOSED_under_ae=sum(r.get('NFX_route')=='(ae)' and r['composed_status']=='CLOSED' for r in rows))
def candidate(base,cert,provider,edges=None):
 row=copy.deepcopy(base);need(cert['function']==row['function'],'wrong function')
 body=cert.get('frozen_body_sha256',cert.get('source_body_sha256',row['frozen_body_sha256']));need(body==row['frozen_body_sha256'],'wrong frozen body')
 need(not cert.get('remaining_inner_hypotheses',cert.get('residual_inner_hypotheses',cert.get('inner_hypotheses_remaining',[]))),'hidden inner hypothesis')
 row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=[provider+'::'+row['function']],open_transitive_dependencies=[])
 cid=cert.get('id',provider+'::'+row['row']);domain=cert.get('domain','caller-established root PacketDomain')
 row['named_hypotheses']=[dict(name=provider+'.'+row['function']+'.PacketDomain',statement=domain,discharged_by=cid),dict(name=provider+'.'+row['function']+'.PhysicalInterpretation',statement='Retained same carrier, ABI, compiler/std/allocator/source-to-ELF and P6/D188 option A',discharged_by=cid)]
 for ob in row['caller_domain_obligations']:
  if provider=='NFG':
   matched=[c for c in cert['call_obligations'] if c['call']==ob.get('call') or ('callee' in ob and ob['callee'] in [re.sub(r'@\d+$','',t) for t in c['call'].get('targets',[])])]
   # Inventory obligations carry the complete original unit-domain record.
   if 'callee' not in ob and 'call' not in ob:matched=[c for c in cert['inventory_obligations'] if all(ob.get(k)==v for k,v in c['original'].items())]
   need(matched and all(c['status']=='CLOSED' and c.get('law') for c in matched),'NFG obligation not covered '+ob['id'])
  if provider=='NFM':
   need(set(cert['parts'])=={'result','state','ordered_effects','native_association'} and not cert['whole_native_output_hypothesis'] and not cert['private_stepby_relation_hypothesis'],'incomplete ad packet')
  if provider=='NFS' and 'callee' in ob:
   edge=next((e for e in edges['overrides'] if e['edge']==row['function']+' -> '+ob['callee']),None);need(edge and edge['status'] in ['CLOSED under (ae)','CLOSED'],'NFS missing incoming domain edge '+ob['id'])
  ob.update(status='CLOSED',discharged_by=cid+'::'+ob['id'])
 # Existing cumulative alternative claim names are historical, not selected uses.
 # Use exact child claims only where selected by the checked packet.
 for ob in row['caller_domain_obligations']:
  if provider in ['NFG','NFM','NFS'] and 'callee' in ob:
   ob['NFX_prior_callee_claims']=ob.get('callee_claims',[])
   ob['callee_claims']=[]
   ob['NFX_domain_certificate']=cid+'::'+ob['id']
 row['active_support_receipts']=[]
 row['NFX_active_support']='Exact source/native support selected by complete replayed '+provider+' certificate; historical quarantined receipts are not selected'
 return row

def build():
 for n in ['NEN','NEZ','NET','NFE','NFK','NFS','NFJ','NFQ']:
  rc=J('evidence/ledger7-20261104/NFX_REPLAY_'+n+'.json');need(rc['exit_status']==0,'predecessor replay failed '+n)
 base=read('evidence/ledger6-20261104/NFK_LEDGER.json');need(len(base['rows'])==587,'inventory size')
 prior.BASE_CREDITS=base['NEZ_credits'];out=copy.deepcopy(base);by={r['row']:r for r in out['rows']};orig={r['row']:r for r in base['rows']};certs={};promotions=[]
 def accept(rid,row,cert,provider,route):
  need(rid in by and row['function']==orig[rid]['function'],'wrong occurrence')
  reasons=prior.row_checks(row,orig[rid],cert);need(not reasons,str(reasons))
  by[rid].update(row);by[rid].update(NFX_provider=provider,NFX_route=route,NFX_rejections=[],NFX_certificate_id=cert.get('id',provider+'::'+rid))
  certs[rid]=cert;promotions.append(rid)
 for cert in J('evidence/slice-q-compose6-20261104/NFG_CERTIFICATES.json'):
  rid=cert['row'];accept(rid,candidate(orig[rid],cert,'NFG'),cert,'NFG','(y) plain')
 for item in J('evidence/slice-q-phase-20261104/NFN_LEDGER_DELTA.json')['promotions']:
  rid=item['row'];need(orig[rid]['composed_status']=='QUALIFIED','geometry qualification missing')
  row=copy.deepcopy(orig[rid]);row['composed_status']='CLOSED';row['NFK_rejections']=[]
  accept(rid,row,dict(id='NFN::'+rid,**item),'NFN','(y) plain')
 for cert in J('evidence/slice-q-mul9-20261104/NFM_CERTIFICATES.json'):
  rid=cert['row'];accept(rid,candidate(orig[rid],cert,'NFM'),cert,'NFM','(ad)')
 ns=J('evidence/slice-q-accum-20261104/NFS_CLOSED.json');edges=J('evidence/slice-q-accum-20261104/NFS_EDGES.json');cc={c['id']:c for c in ns['certificates']};edges['overrides']=edges['overrides']+J('evidence/slice-q-mul9-20261104/NFM_EDGES.json')['edges']
 for rid,entry in ns['rows'].items():
  cert=cc[entry['certificate']];accept(rid,candidate(orig[rid],cert,'NFS',edges),cert,'NFS','(ae)')
 d=read('evidence/slice-d-define-20261104/NFQ_COMPOSED_LEDGER.json');dc=J('evidence/slice-d-define-20261104/NFQ_CERTIFICATES.json')
 for rid,cert in dc.items():accept(rid,next(r for r in d['rows'] if r['row']==rid),cert,'NFQ','(y) plain')
 for row in out['rows']:
  row.setdefault('NFX_provider',row.get('NFK_provider',row.get('NEZ_provider',row.get('NEN_slice','inherited'))))
  route='reclassification' if row.get('NEZ_support_route','').startswith(('D188_','z(1)')) else '(y) plain'
  row.setdefault('NFX_route',route if row['composed_status']=='CLOSED' else None);row.setdefault('NFX_rejections',row.get('NFK_rejections',row.get('NEZ_rejections',[])))
  row['NFX_transport']='P6/D188 option A retained/reclassified; never removed' if row['composed_status']=='CLOSED' else None
  row['NFX_trust_rows']=sorted(set(row.get('NFK_trust_rows',[])))
  if row['composed_status']=='CLOSED':row['NFX_trust_rows'].append('NativeContractSemanticTransport')
 # Fresh combined coherence audit can only deny credit, never create it.
 if (E/'NFX_COHERENCE_DENIALS.json').exists():
  for denial in J('evidence/ledger7-20261104/NFX_COHERENCE_DENIALS.json'):
   row=by[denial['row']];need(row['composed_status']=='CLOSED','denial not a credited row');row['composed_status']='QUALIFIED';row['NFX_rejections']=[denial['reason']]
 # Preserve the predecessor's selected-claim denial propagation. An alternate
 # certified route may retain a claim only when it is actually selected CLOSED.
 changed=True
 while changed:
  changed=False
  denied={claim for r in out['rows'] if r['composed_status']!='CLOSED' for claim in r['selected_claims']}
  accepted={claim for r in out['rows'] if r['composed_status']=='CLOSED' for claim in r['selected_claims']}
  for row in out['rows']:
   if row['composed_status']!='CLOSED':continue
   bad=sorted({c for ob in row['caller_domain_obligations'] for c in ob.get('callee_claims',[]) if c in denied and c not in accepted})
   if bad:
    row['composed_status']='QUALIFIED';row['NFX_rejections']=['Selected callee is QUALIFIED under combined coherence: '+', '.join(bad)];changed=True
 spec=J('docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices'];ds=J('evidence/slice-d-define-20261104/NFQ_SLICE_D.json')['slices']['D'];spec={**spec,'D':ds}
 slices={}
 for lane in ['S','Q','D']:
  rows=[r for r in out['rows'] if r['function'] in spec[lane]['functions']];roots=[]
  for f in spec[lane]['roots']:
   rr=[r for r in rows if r['function']==f];need(rr,'missing root '+f)
   status='CLOSED' if all(r['composed_status']=='CLOSED' for r in rr) else 'QUALIFIED' if any(r['composed_status']=='QUALIFIED' for r in rr) else 'OPEN'
   roots.append(dict(function=f,rows=[r['row'] for r in rr],status=status))
  slices[lane]=dict(**counts(rows),functions=len(spec[lane]['functions']),roots=roots,roots_CLOSED=sum(x['status']=='CLOSED' for x in roots),per_tx={tx:counts([r for r in rows if r['transaction']==tx]) for tx in ['TX1','TX2']})
 outside=[r['row'] for r in out['rows'] if not any(r['function'] in spec[x]['functions'] for x in spec)]
 need(outside==['TX2:046','TX2:211'],'inventory defects changed')
 for r in out['rows']:need((r['row'],r['function'],r['frozen_body_sha256'])==(orig[r['row']]['row'],orig[r['row']]['function'],orig[r['row']]['frozen_body_sha256']),'identity drift')
 per_function={f:dict(**counts([r for r in out['rows'] if r['function']==f]),rows=[r['row'] for r in out['rows'] if r['function']==f]) for f in sorted({r['function'] for r in out['rows']})}
 out['NFX_per_function']=per_function
 out['NFX_unique_functions']=dict(total=len(per_function),fully_CLOSED=sum(v['CLOSED']==v['total'] for v in per_function.values()),with_QUALIFIED=sum(v['QUALIFIED']>0 for v in per_function.values()))
 out['NFX_per_tx']={tx:counts([r for r in out['rows'] if r['transaction']==tx]) for tx in ['TX1','TX2']}
 out['NFX_D_transaction_roots']=[dict(row=r['row'],function=r['function'],status=r['composed_status']) for r in out['rows'] if r['function'] in ds['roots']]
 out.update(NFX_source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),NFX_headline='AspisR1.RPx_Deployed.deployed',NFX_coverage=counts(out['rows']),NFX_slices=slices,NFX_inventory_defects=outside,NFX_newly_admitted=sorted(promotions),NFX_certificates=certs,NFX_security_target_established=False,NFX_cold_release_replay=False,NFX_historical_fields='Only NFX fields and composed_status govern this checkpoint; NFK/NEN/NEZ fields are preserved history')
 routes={r['row']:dict(function=r['function'],status=r['composed_status'],route=r['NFX_route'],provider=r['NFX_provider'],trust_rows=r['NFX_trust_rows'],transport=r['NFX_transport'],certificate=r.get('NFX_certificate_id'),reason=r['NFX_rejections']) for r in out['rows']}
 closed=[r for r in out['rows'] if r['composed_status']=='CLOSED']
 trust=[]
 for t in base['trust_rows']:
  t=copy.deepcopy(t);t['status']='ACCEPTED retained trust';t.pop('NFK_classification',None);t.pop('NFK_ruling',None)
  if t['id']=='RuntimeReturnData':t.update(classification='ACCEPTED; narrowed by (ab\')',scope='For 1 <= |b| <= 1024: set_return_data(b) by P; immediate get_return_data in same instruction context with no intervening CPI returns Some((P,b)) exactly. Aspis ASR8 is 792 bytes. Empty replies excluded. Pool caller/program-id/context association remains OPEN.')
  if t['id']=='RuntimeMemcmp':t['classification']='ACCEPTED (ac); retained runtime implementation assumption'
  t['direct_closed_rows']=[r['row'] for r in closed if t['id'] in r['NFX_trust_rows']]
  t['root_context_retained']='All eventual headline applications retain this hypothesis where its exact typed statement requires it; no inference that every helper calls this syscall.'
  trust.append(t)
 for ident,scope in [('S2TrustedSdkBorrow','Adopted route B SDK AccountInfo/RefCell fifteen-field contract; concrete caller observations still proved separately'),('TrustedStd','Retained standard-library/copy behavior on exact valid domains; no Pool Vec credit inferred'),('AllocatorABICompilerSourceToELF','Retained realization boundary; concrete final artifact binding remains L188, not discharged by cached proof imports')]:
  trust.append(dict(id=ident,status='RETAINED ROOT REALIZATION OBLIGATION' if ident=='AllocatorABICompilerSourceToELF' else 'ACCEPTED retained trust',scope=scope,direct_closed_rows=[],root_context_retained='Explicit conditional root realization, not a proved implementation property'))
 out['trust_rows']=trust
 return out,routes,dict(rows=trust,scope='Direct row tags and explicitly retained headline context are distinguished; no trust item discharged.',headline='AspisR1.RPx_Deployed.deployed')

def markdown(d):
 lines=['# Ledger refresh 7','','**Target not yet established.** All 587 frozen composed occurrences are retained. CLOSED means conditional hybrid source composition on the stated domain; it does not mean deployed security or a cold release replay.','','| Scope | Total | CLOSED | CLOSED under (ae) | QUALIFIED | OPEN |','|---|---:|---:|---:|---:|---:|']
 for k,v in [('all',d['NFX_coverage']),*[(k,d['NFX_slices'][k]) for k in ['S','Q','D']]]:lines.append(f"| {k} | {v['total']} | {v['CLOSED']} | {v['CLOSED_under_ae']} | {v['QUALIFIED']} | {v['OPEN']} |")
 lines+=['','D has 0/2 transaction root occurrences CLOSED, represented by one common function. Slice memberships overlap: four Q/S occurrences count once globally. D is disjoint from Q/S. TX2:046 (unresolved WideExact::from_m31) and TX2:211 (omitted map_err(error) callback) are inventory defects outside D ∪ Q ∪ S, retained OPEN.','']
 for lane in ['S','Q','D']:
  s=d['NFX_slices'][lane];lines+=['',f"Slice {lane}: {s['roots_CLOSED']}/{len(s['roots'])} roots CLOSED; {s['functions']} inventoried functions.",'','| Root | Status | Rows |','|---|---|---|']
  lines += [f"| {r['function']} | {r['status']} | {', '.join(r['rows'])} |" for r in s['roots']]
 lines+=['','The (ad) route uses the corrected 26 term iterations and seven cuts. The (ae) column is separate because the K-2 quarantine remains for other Option<fn> shapes. P6/D188 option-A semantic transport is retained/reclassified, never removed. RuntimeReturnData (nonempty scope, 792-byte ASR8), RuntimeMemcmp and RuntimePersistence are ACCEPTED retained trust; NativeContractSemanticTransport and runtime sha256 = H remain explicit. Full direct-use lists and scopes: NFX_TRUST_USED.json.','',
 'If all three slices, including repair of S coherence, the D roots and remaining boundaries were CLOSED, the composed theorem would connect the SAME accepted frozen deployed TX1/TX2 native executions, original proof/public bytes, 1768-byte saved checkpoint, ordered calls/state/effects and Pool settlement to the adopted frozen3 experiment in AspisR1.RPx_Deployed.deployed. Its existing conditional bound failureModel ≤ (Q0+Q1+1)/2^100 on the declared maxQueries range, and its strict zero-query margin, would then transfer under their exact hypotheses and explicit trust inventory. This states the existing theorem; it does not replace the 100-bit per-attempt release contract. This would not by itself remove cryptographic, SDK/std/allocator/ABI/runtime/source-to-ELF premises, nor replace the 100-bit per-attempt release requirement with work-normalised or grinding credit. No such composed theorem is claimed today.','',
 'The new coherence result additionally requires retargeting the 89 QUALIFIED S occurrences (85 direct legacy dependencies and four selected-callee consequences). Source-validator S remains 7/7 roots CLOSED historically, but headline-coherent S is 0/7 today.','',
 'Remaining: the D entry/driver roots and all incoming domains (including Prepared/powers/prepare), Pool return-data/program-id/same-instruction/carrier and settlement join, L159/L181 concrete realization obligations under the native route, L187 cold coherent dependency replay, L188 final trust/axiom/source/artifact audit, and the two inventory defects. Existing release-route reclassifications of L159/L181 are not native proof discharges. Privacy and the two-transaction design remain unchanged.','',
 'Coherence: NFX_AUDIT.json records the combined import, exact raw NEP ax2 walks, fixtures and module scan. A failed or legacy-dependent packet receives QUALIFIED, even when its original source validator reports CLOSED. The legacy forest and its 650 inherited references are excluded from authoritative coherent credit.','',
 '| Row | Function | Status | Route | Trust used | Reason |','|---|---|---|---|---|---|']
 for r in d['rows']:lines.append(f"| {r['row']} | {r['function']} | {r['composed_status']} | {r['NFX_route'] or ''} | {', '.join(r['NFX_trust_rows'])} | {'; '.join(r['NFX_rejections'])} |")
 return '\n'.join(lines)+'\n'

def main():
 d,r,t=build()
 for name,obj in [('NFX_LEDGER.json',d),('NFX_ROUTES.json',r),('NFX_TRUST_USED.json',t)]:
  raw=(json.dumps(obj,sort_keys=True,indent=1)+'\n').encode();p=E/name
  if len(raw)>20_000_000:p.with_suffix(p.suffix+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_suffix(p.suffix+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
  else:p.write_bytes(raw)
 (E/'NFX_LEDGER.md').write_text(markdown(d));print(json.dumps(dict(coverage=d['NFX_coverage'],slices=d['NFX_slices'])))
if __name__=='__main__':main()
