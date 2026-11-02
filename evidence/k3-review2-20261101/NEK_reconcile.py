"""Explain every removed historical dependency using selected certificates."""
from NEK_scan import *
old=read_json(E/'NEK_CLOSURE_FLAT_PROVISIONAL.json');new=read_json(E/'NEK_CLOSURE.json');index={r['row']:r for r in old['rows']};Q=read_json(ROOT/'evidence/slice-q-compose-20261029/NEB_EDGES.json');out=[]
for r in new['rows']:
 before={k['receipt'] for k in index[r['row']]['closure']['kani']};after={k['receipt'] for k in r['closure']['kani']};removed=sorted(before-after)
 if not removed:continue
 certs=[c for c in Q['row_certificates'] if c['function'] in r['closure']['functions']]
 sources=[]
 for c in certs:
  refs={}
  for key in ['review','native_review']:
   if key in c:
    q=c[key];p=ROOT/q['path'];b=p.read_bytes() if p.exists() else subprocess.check_output(['git','show','HEAD:'+q['path']]);assert sha(b)==q['sha256'];refs[key]=q
  sources.append(dict(certificate=c['id'],function=c['function'],selected_claims=c['selected_claims'],references=refs))
 out.append(dict(row=r['row'],function=r['function'],historical_receipts_removed_from_active_closure=removed,retained_active_receipts=sorted(after),selected_claims=r['closure']['claims'],canonical_call_edges=r['closure']['edges'],selected_certificates=sources,reason='flat row receipt lists aggregate discovery/superseded unit evidence; current selected claims plus exact content-addressed native row/edge certificates and actual canonical call dependencies govern active support; no receipt or historical verdict deleted'))
(E/'NEK_DEPENDENCY_RECONCILIATION.json').write_text(json.dumps(dict(previous='NEK_CLOSURE_FLAT_PROVISIONAL.json',active='NEK_CLOSURE.json',rows=out,active_kani_receipts=len({k['receipt'] for r in new['rows'] for k in r['closure']['kani']}),unrelated_blockers_forbidden=True,scope='K-3 only; existing certificate trust/domain qualifications retained'),indent=2)+'\n');print('reconciled',len(out),'rows')
