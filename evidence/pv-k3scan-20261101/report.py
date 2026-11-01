"""Render conservative per-credit recommendations; never writes the privacy ledger."""
from pathlib import Path
import json,lzma,collections,re,hashlib
E=Path(__file__).resolve().parent
def load(p):
 q=E/p
 if q.exists():return json.loads(q.read_text())
 return json.loads(lzma.decompress(q.with_suffix(q.suffix+'.xz').read_bytes()))
credits=load('CREDITS.raw.json');scoped={v['receipt']:v for v in load('SELECTED-STANDALONE-SCOPES.json')};rows=load('rows9.json');pins=load('PINS.json');idx=load('SOURCE_INDEX.json');result=[]
kmx={'K04':'V179','K06':'V179','K08':'V182','K12':'V179','K14':'V182','K22':'V195','K24':'V195','K26':'V233','K28':'V233'}
kmx_control={'K04':'K05','K06':'K07','K08':'K09','K12':'K13','K14':'K15','K22':'K23','K24':'K25','K26':'K27','K28':'K29'}
def harnesses(x):
 tail=x['harness'].split('::')[-1];found=[]
 for name,m in x['matched_rust'].items():
  text=(E/'blobs'/(m['sha256']+'.rs')).read_text(errors='replace')
  for a in re.finditer(r'\bfn\s+'+re.escape(tail)+r'\s*\(',text):
   start=text.rfind('#[kani::proof',0,a.start())
   if start<0 or a.start()-start>2500:start=a.start()
   brace=text.find('{',a.end());depth=0;end=brace
   if brace<0:continue
   for end in range(brace,len(text)):
    depth+=(text[end]=='{')-(text[end]=='}')
    if depth==0:break
   span=text[start:end+1];hh=hashlib.sha256(span.encode()).hexdigest()
   if hh not in [v['sha256'] for v in found]:
    found.append({'input':name,'sha256':hh,'line':text[:start].count('\n')+1,'stub_attributes':re.findall(r'#\[kani::stub(?:_verified)?\((.*?)\)\]',span,re.S),'text':span})
 return found
for i,x in enumerate(credits):
 h=x['harness'];ledger=x.get('ledger_rows',[]);p=x['path'];extra=None;ctl=None
 if '/pv-kstub-' in p:
  run=p.split('/')[-2];ledger=[kmx[run]];ctl='evidence/pv-kstub-20261028/'+kmx_control[run]+'/receipt.json'
 elif '/pv-b3p6-' in p:
  ledger=['V244'];extra='Local op227 body support; not whole V244 closure'
  for pos,neg in [('K73946','K73945'),('K73948','K73947'),('K73950','K73949')]:
   if '/'+pos+'/' in p:ctl='evidence/pv-b3p6-20261028/resume17/'+neg+'/receipt/receipt.json'
 elif not ledger and ('pv-l2c-' in p):ledger=['V352','V354','V357','V360'];extra='Supporting parser observation / aggregate copy; no new gate'
 elif not ledger and ('pv-srcid3-' in p):ledger=['V163','V165','V167'];extra='Read-only copied receipt of prior RunJoin source-root gate'
 elif not ledger and ('pv-dlib-' in p):ledger=['V185'];extra='Supporting generic length-only scope; no full source restoration'
 selected=harnesses(x);stubs=sorted(set(t.strip() for f in selected for t in f['stub_attributes']))
 r=x['receipt'];declared=r.get('stubs')
 if not stubs and declared:stubs=declared if isinstance(declared,list) else [str(declared)]
 stub_note='; '.join(stubs) if stubs else 'none in recovered selected harness' if selected else 'unrecorded (OPEN)'
 static=x.get('writable_static_candidates',[])
 oracle='local / no selected global log recovered' if not static and selected else 'recorded-input static candidates; selected association unresolved' if static else 'unrecorded (OPEN)'
 if 'shared_repeat16' in h or ('K73931/' in p or 'K73932/' in p):oracle='shared_callee16::{USED,TAG,LEFT,RIGHT,OUT}; mutable global memo oracle'
 classification=scoped[x['path']]['classification'] if x['path'] in scoped else x['classification']
 status='UNAFFECTED' if classification in ('UNAFFECTED','NOT-EXPOSED') else 'SUSPENDED'
 why='K-3 clearance limited to recovered recorded inputs' if status=='UNAFFECTED' else 'Missing input / macro / selected source association; no admissible K-3 restoration'
 if x.get('k1_status')=='EXPOSED':status='SUSPENDED';why+='; historical K-1 copy suspension also remains'
 if 'EXCLUDED' in x.get('k1_use',''):status='WITHDRAWN';why='Inherited excluded allocator diagnostic: never an accepted application credit'
 if ctl:why+='; historical matched control retained but does not discharge unresolved closure'
 result.append({'credit_id':f'C{i+1:03d}','ledger_rows':ledger,'harness':h,'receipt':p,'receipt_sha256':x['sha256'],'branch':x['branch'],'revision':x['revision'],'historical_refs':x.get('historical_refs',[]),'k1_index':x.get('k1_index'),'classification':classification,'selected_scope_evidence':scoped.get(x['path']),'raw_classification':x['raw_classifier']['classification'],'raw_reason':x['raw_classifier']['reason'],'stubs':stubs,'stub_note':stub_note,'oracle':oracle,'selected_harness_sources':selected,'matched_sources':x['matched_rust'],'missing_sources':x['missing_rust'],'macro_sources':x['raw_classifier']['macro_sources'],'static_sites':x['raw_classifier']['static_sites'],'rerun':'not re-run; unresolved closure or inherited non-credited support' if status!='UNAFFECTED' else 'not required by K-3 on recovered recorded inputs','matched_control':ctl,'final_status':status,'reason':why,'scope_note':extra})
# Save compact review index separately from complete receipt-pinned/raw source evidence.
(E/'CREDITS.json').write_text(json.dumps(result,indent=2)+'\n')
summary={'observations':len(result),'historical_k1_entries':len({x['k1_index'] for x in result if x['k1_index'] is not None}),'classification':dict(collections.Counter(x['classification'] for x in result)),'final_status':dict(collections.Counter(x['final_status'] for x in result)),'lean_used':0,'new_kani_runs':0,'endpoint_premises_removed':0}
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
header='''# K-3 Stream B credit audit (D545)

Privacy target not established. These are recommendations for the lead; the ledger is not edited. `UNAFFECTED` concerns K-3 on the recovered, recorded Rust inputs only. It does not release K-1, K-2, std parity, compiler cohort, native association or whole-row obligations.

The exact ab9c588335 classifier and its four requested inputs were read before use. Its unchanged NEH_check.py passed 29 retained diagnostics plus macro, missing-input and local-record boundary cases. Its native labels are AFFECTED / UNAFFECTED. AFFECTED plus incomplete input or macro closure is reported OPEN, including when a writable-static candidate is also visible. Six NOT-EXPOSED entries have a mechanically checked selected standalone module closure: the per-run freeze inventories several unrelated packages, but the exact selected Cargo manifest has no dependencies/build script, and every selected root/reference/KMX module is recovered by that run's hash and passes the unchanged classifier. No such clearance is made for an unrecorded expansion or stub. SELECTED-STANDALONE-SCOPES.json records the module/manifest association and the excluded inventory entries. Raw sites and reasons remain in CREDITS.raw.json.xz; per-credit selected harness spans, stubs, input hashes and provenance are in CREDITS.json.xz.

Inventory: all 264 historical PASS observations in the prior complete K-1 census, plus later/additional PASS observations from pinned branch receipts. Historical observations include partial/superseded support and copied receipts, not that many currently credited row closures. The 407-row coverage review below distinguishes current row support. Codegen-only runs, failing controls and failed/time-out verification attempts are retained in RECOVERED.json but are not passing credits.

V201/V220/V237's latest rdcd4 restorations are independent of Kani: REPORT.md explicitly records 0 Kani. They remain UNAFFECTED by K-3 at their current structural/extraction/singleton scopes. Their historical supporting Kani observations are still audited below. V265's current structural restoration also does not consume its quarantined pointer-form Kani route. Its pointer form remains quarantined under (r''); no rename or Kani result here releases it.

K73950 and all five (k-triple-prime) releases are included. The 23 ordinary std structural arguments are a distinct (k-triple-prime) qualification, not a K-3 classifier clearance. Existing intrinsics/generated glue retain V370 / D381 / D386. The historical b3p6 hand audit is retained as inputs/b3-k3.json; unused global-oracle files and macro closure are not silently dropped from its recorded source map.

A global log embedded in a cfg-only native step cannot be replaced by a local mock while retaining the same property. Such source/stub associations remain SUSPENDED pending a checked local-context native-step association. Missing original inputs also cannot be replaced by current same-name files. Unresolved macro closure cannot be repaired by an unrelated passing assertion. No narrowed or synthetic replacement is labelled RESTORED.

## Per-credit recommendations

Each row is one PASS observation. Ledger cells name the original row(s), not an assertion that the entire row was closed by Kani. Receipt contents and exact branch/source pins are recoverable from the JSON indexes. Stub/oracle details below are conservative selected-source inventory; a missing selection is explicit.

| Credit | Ledger row(s) | Harness | Classification | Stubs / oracle | Receipt / branch | Re-run and final status |
|---|---|---|---|---|---|---|
'''
lines=[header]
for x in result:
 def clean(s):return str(s).replace('|','\\|').replace('\n',' ')
 stub=x['stub_note'];stub=stub if len(stub)<170 else stub[:167]+'… (full list in JSON)'
 lines.append('| '+ ' | '.join(map(clean,[x['credit_id'],', '.join(x['ledger_rows']),f"`{x['harness']}`",x['classification'],stub+' / '+x['oracle'],f"`{x['receipt']}`; `{x['branch']}`",x['rerun']+'; **'+x['final_status']+'**']))+' |\n')
(E/'K3-CREDITS.md').write_text(''.join(lines))
covered=collections.defaultdict(list)
for x in result:
 for row in x['ledger_rows']:covered[row].append(x['credit_id'])
review=[]
for r in rows:
 rid=r['id'];ids=covered[rid];route=r.get('closure_route')
 if rid in ['V177','V180']:decision='NOT-EXPOSED for the selected current PathBuf gate; older copied gate remains suspended; retain every original native/std/deployment qualification'
 elif rid in ['V201','V220','V237']:decision='UNAFFECTED: latest rdcd4 restoration uses 0 Kani; historical supporting gates listed separately'
 elif route=='P6 gate' and r.get('recount9_status')=='CLOSED-ON-CANDIDATE':decision='Current bounded native association depends on Kani; OPEN inputs require lead suspension until controlled restoration and std qualification'
 elif ids:decision='Historical/partial Kani support audited; preserve independent structural/extraction/model law and original open deployment obligations'
 else:decision='No Kani-dependent credit identified at recount8/9 and the requested later restorations'
 review.append({'ledger_row':rid,'name':r['name'],'recount9_status':r.get('recount9_status'),'closure_route':route,'credits':ids,'decision':decision})
(E/'ROW-COVERAGE.json').write_text(json.dumps(review,indent=2)+'\n')
(E/'ROW-COVERAGE.md').write_text('# All 407 ledger rows reviewed\n\n| Row | Recount9 status / route | Kani observation(s) | K-3 disposition at original scope |\n|---|---|---|---|\n'+''.join(f"| {x['ledger_row']} | {x['recount9_status']} / {x['closure_route']} | {', '.join(x['credits']) or 'none'} | {x['decision']} |\n" for x in review))
print(json.dumps(summary))
