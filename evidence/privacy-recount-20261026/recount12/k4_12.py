"""Conservative k4 credit overlay; no Kani invocations."""
import json,lzma,re,hashlib,subprocess
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
old=json.loads((B/'recount11/k3-final-credits11.json').read_text())
pins=json.loads((P/'pins.json').read_text())['revisions'];rev=pins['k3scan']
raw=subprocess.check_output(['git','show',rev+':evidence/pv-k3scan-20261101/CREDITS.json.xz']);credits=json.loads(lzma.decompress(raw));historical=[]
# Include safe get queries in the review set: their input is unconstrained even
# though std checks bounds before dereference. Do not silently use that source
# argument as the user-requested retained counterexample trace.
sensitive={'C044':('i','PathBuf bytes get(i), twice; source checks i<len before dereference','K79200','K79201'),
'C084':('i','String/Path bytes get(i); source checks i<len before dereference','historical K13','historical K13 control'),
'C088':('k','tail.get(k) and reference tail.get(k); b/j guarded and n<=64','K79220','K79221'),
'C089':('k','tail.get(k) and reference tail.get(k); b/j guarded and 64<n<=129','K79222','K79223')}
for prior,c in zip(old,credits):
 assert prior['credit_id']==c['credit_id'];id=c['credit_id'];active=prior['final_status'] in ['RESTORED','UNAFFECTED']
 z={'credit_id':id,'harness':c['harness'],'ledger_rows':c['ledger_rows'],'k3_status':prior['final_status'],'k4_status':prior['final_status'],'inputs':'git:'+rev+':evidence/pv-k3scan-20261101/CREDITS.json.xz#'+id,'selected_harness_sources':c['selected_harness_sources'],'source_closure_manifest':'git:'+rev+':evidence/pv-k3scan-20261101/CREDITS.json.xz#'+id+'/matched_sources'}
 if not active:z['screen']='Already uncredited: historical K-1/K-2/K-3 restrictions retained; no new k4 credit'
 elif id in sensitive:
  index,why,pos,control=sensitive[id];z.update(screen='FULL_WIDTH_INPUT_REVIEW',index=index,source_bounds=why,positive=pos,control=control,trace_location=None,trace_verdict='MISSING retained full control execution trace. Receipt/FAIL assertion summaries are not a pointer/offset trace.',k4_status='SUSPENDED',reason='Conservative k4 withholding: full-width query remains unconstrained at harness input; no retained full matched trace confirms intended reason. Source get bounds make 48-bit aliasing unlikely here, but are not substituted for the requested trace. No aliasing claimed; no Kani rerun.')
 else:z['screen']='No unconstrained full-width object index: scalar-only, fixed literal/bounded loops, bounded array indices, or checked small-domain source access; historical source closure and newer local-record overlays retained'
 historical.append(z)
# New gates at all pins. A successful positive is a potential credit, never
# inferred from aggregate process status (matched controls intentionally fail).
entries=json.loads((P/'kani-receipt-census12.json').read_text());objs=json.loads(lzma.decompress((P/'kani-receipt-inputs12.json.xz').read_bytes()));new=[];seen=set()
for e in entries:
 key=(e['id'],e['receipt_blob'])
 if key in seen:continue
 seen.add(key)
 logs=[(p,objs.get(b,'')) for p,b in e['files'].items() if p.endswith(('output.log','stdout.log'))]
 outcomes=[]
 for path,s in logs:
  for m in re.finditer(r'Checking harness (.*?)\.\.\.([\s\S]*?)(?=Checking harness|Manual Harness Summary:|\Z)',s):
   v=re.search(r'VERIFICATION:- (SUCCESSFUL|FAILED)',m[2]);failure=re.search(r'Failed Checks: ([\s\S]*?)(?=VERIFICATION:-)',m[2])
   outcomes.append({'harness':m[1],'verdict':v[1] if v else 'NO_VERDICT','assertion_summary':failure[1].strip() if failure else None,'output':path})
 positives=[o for o in outcomes if o['verdict']=='SUCCESSFUL' and not re.search(r'wrong|control|negative',o['harness'],re.I)]
 z={'id':e['id'],'ref':e['ref'],'revision':e['revision'],'receipt':e['path'],'receipt_blob':e['receipt_blob'],'outcomes':outcomes,'potential_credit':bool(positives),'k4_disposition':'No unconstrained full-width physical index identified; all other historical restrictions retained' if positives else 'No positive credit inferred; failed/unsupported/stopped/prototype evidence retained'}
 if e['id'] in ['K93100','K93108']:
  z.update(k4_disposition='NO CREDIT — positive frame model error: 48-bit pointer offset aliasing',trace_location='git:'+pins['stx']+':evidence/pv-stx-20261104/D637/K93108/positive-frame-trace.txt',reason='Distinct full-width offsets differ by 2^62 and both reduce to 2^48-4. Classified before further credit; not a native source violation.')
 if e['id'] in ['K93109','K93110','K93111']:
  z.update(k4_disposition='SUSPENDED (retained full matched trace missing)',trace_location=None,reason='Full-width index/query are segregated into logical u128 offsets and a two-slot pointer projection. Source repair avoids the alias mechanism, but retained output is terse assertion evidence, not a full control trace. Conservatively withhold k4 credit; original ptr.add/allocation/OWNER association remains OPEN.',source='git:'+pins['stx']+':tools/pv-stx-20261104/clone-certificate/src/indexed.rs')
 if e['id'] in ['K93101','K93102','K93103','K93105','K93106','K93107']:
  z['k4_disposition']='Selected-place segment only: unbounded index/capacity remain scalar; actual physical accesses are fixed Window.slot/prefix/suffix, lanes<WORDS. No original arbitrary-offset certificate; original pointer/OWNER association OPEN.'
 if e['id']=='K92679' and e['ref']=='stxb':z['k4_disposition']='NO CREDIT — recorded one-scope overlap, replaced sequentially by changed K92680'
 if e['ref']=='evhB':z['k4_disposition']='No native task/spawn credit: TLS/capture controls unreached or layout-only diagnostic; no thread contract discharged'
 if e['id'] in ['K91910','K91911','K91921']:
  z['k4_disposition']='NO restored credit: C156 remains K-3 SUSPENDED; local memo/caller diagnostics do not supply full-raw mul bridge'
 if e['id'] in ['K92607','K92609','K91901','K91912']:z['k4_disposition']='Superseded prototype; no independent current credit'
 new.append(z)
from collections import Counter
result={'policy':'Conservative full-width-input census, including checked get queries and segregated logical projections. Suspension for missing execution trace is an evidence suspension, not an allegation of aliasing. No new bound or assumption, no Kani rerun. All new positive gates inventoried, including superseded and uncredited diagnostics.',
'k3_before_k4':dict(Counter(x['k3_status'] for x in historical)),'after_k4':dict(Counter(x['k4_status'] for x in historical)),
'historical_credits':historical,'new_K9_gates':new,'historical_suspensions':list(sensitive),'new_projection_suspensions':['K93109','K93110','K93111'],
'actual_aliasing':['K93100','K93108'],'Kani_runs':0,
'limitations':'No full negative trace was regenerated. Terse FAIL output is stored as assertion summary only. Bounded/guarded sources are excluded from alias-risk findings, but unconstrained get input queries are conservatively withheld until trace evidence is retained. K-3 status and k4 status are distinct fields.'}
if (P/'k4-credit-check.json').exists():
 prior_check=json.loads((P/'k4-credit-check.json').read_text())
 for z in result['historical_credits']:
  before=next(a for a in prior_check['historical_credits'] if a['credit_id']==z['credit_id'])
  for field in ['retained_summary','trace_path_inventory']:
   if field in before:z[field]=before[field]
result['source_screen']='source-screen12.json';result['current_support']='current-support12.json'
(P/'k4-credit-check.json').write_text(json.dumps(result,indent=1)+'\n')
(P/'k3-final-credits12.json').write_text(json.dumps([dict(x,k4_status=historical[i]['k4_status']) for i,x in enumerate(old)],indent=1)+'\n')
print('k3',result['k3_before_k4'],'k4',result['after_k4'],'new gates',len(new))
