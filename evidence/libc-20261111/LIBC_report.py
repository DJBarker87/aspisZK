from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
spec=json.loads((E.parent/'lib-map-20261107/LIB0_MAP.json').read_text())
# Concrete field graphs; builders remain explicit until the other lane's bundle exists.
fields={
'filled':('LIBC_Filled','model_port','n≤32768; native zero byte/identity Clone'),
'expandSemantic':('LIBC_ExpandSemantic','model_port','7015 input /13831 output, arbitrary bytes'),
'expandValues':('LIBC_ExpandValues','model_port','source≤1856/output≤3712; guard failures included'),
'wideView':('LIBC_WideView','model_port','proof57607/semantic13831/y1 928'),
'parseShape':('LIBC_ParseShape','source','proof57607; source checks remain outcomes'),
'canonicalScan':('LIBC_CanonicalScan','model_port','proof57607; all source checks remain outcomes'),
'accNew':('LIBC_AccNew','source','literal S2; both reservation outcomes'),
'weightsNew':('LIBC_WeightsNew','source','64 canonical original weights; same runtime reservation'),
'finish':('LIBC_Finish','source','original pending/accumulator pair invariant'),
'batchMerkle':('LIBC_BatchMerkle','returning','NLO-bf64–67 verbatim; batch0; SAME proof/queries/roots/folded root'),
'geometry':('LIBC_Geometry','source','deployed0..10 or10..22; canonical distinct original queries'),
'queryLoop':('LIBC_QueryLoop','source','original packet invariant; TX1 finish10, accumulator.next0'),
'checkpoint':('LIBC_Checkpoint','run_model','current-pair DriverEstablishedDomain; stored57607/public1880'),
}
accepted={}
validation=[]
for p in sorted(E.glob('LIBC_L[0-9][0-9][0-9]/receipt.json')):
 j=json.loads(p.read_text());k={x:j.get(x) for x in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','limits','print_axioms']};k['receipt']=str(p.relative_to(E));validation.append(k)
 if j['exit_status']==0:accepted[j['module']]=j
(E/'LIBC_VALIDATION.json').write_text(json.dumps(validation,indent=1)+'\n')
status={'target_established':False,'row_credit_claimed':False,'budget':{'authorized_scopes':300,'used_scopes':len(validation),'kani':0,'extraction':0},'modules':{},'fields':{}}
closed=[];clauses=[]
for f,(m,t,d) in fields.items():
 ok=m in accepted
 status['fields'][f]={'status':'DONE' if ok else 'WAITING','module':m,'theorem':m+'.'+t,'domain':d,'reason':None if ok else 'focused compilation pending','remaining':'LIB_ bundle/principal caller instantiation and ledger review; no row credit'}
 supplying=[x for x in spec['fields'] if x['field']==f]
 closed.append({'field':f,'defining_term':m+'.child','bridge':m+'.'+t,'source':m+'.lean','supplying':[z for x in supplying for z in x['supplying']],'hypotheses':[{'class':'original_own_argument_domain','clause':d},{'class':'universally_quantified_data','clause':'SAME original arguments and Env'},{'class':'retained_runtime_realization','clause':'Env backend and reservation are model inputs; native runtime realization remains the existing integration trust item, not newly proved totality'}],'added_trust':[],'row_credit_claimed':False})
 clauses.append({'field':f,'domain':d,'classification':'retained CLOSED caller clause; own-input model graph','caller_discharge':'principal composition outside this lane','source':m+'.lean'})
for n,m in [(19,'LIBC_VPrepare'),(20,'LIBC_VTx1A'),(21,'LIBC_VTx1B')]:
 status['modules'][str(n)]={'status':'DONE' if m in accepted else 'WAITING','module':m,'scope':accepted.get(m,{}).get('attempt'),'remaining':'Concrete field exports only; final VLib bundle belongs to LIB_'}
for f,m,n,reason in [('PreparedNew','LIBC_Prepared',23,'All operational content fixed; ten carrier type equalities need the actual LIB_ VL* bundle. Original upstream semantic/expanded provenance must be discharged by principal.'),('S1Lib','LIBC_S1',24,'All six fields fixed; publicDom compatibility is proved by LIBC_S1Validated.validated at the SAME statement. Public type identity still needs actual LIB_ VL* bundle.')]:
 status['fields'][f]={'status':'WAITING','module':m,'reason':reason,'support_compiled':m in accepted}
 status['modules'][str(n)]=status['fields'][f]
 closed.append({'field':f,'defining_term':m+'.child V types' if n==23 else m+'.library V tyPublic','source':m+'.lean','hypotheses':[{'class':'carrier_equalities','clause':'Only type identities, to be discharged by rfl at actual VL*; no operational dictionary or child-success premise'},{'class':'original_own_argument_domain','clause':'See '+('LIBC_PreparedDomain.lean' if n==23 else 'S1 domain True; source allocation probe LIBC_FirstBox.lean')}],'added_trust':[],'remaining':[reason],'row_credit_claimed':False})
(E/'LIBC_STATUS.json').write_text(json.dumps(status,indent=2)+'\n')
(E/'LIBC_CLOSED.json').write_text(json.dumps(closed,indent=2)+'\n')
(E/'LIBC_CALLER_CLAUSES.json').write_text(json.dumps(clauses,indent=2)+'\n')
print(json.dumps({'receipts':len(validation),'fields':{k:v['status'] for k,v in status['fields'].items()}}))
