"""Summarize receipts without converting fragments into composed-row credit."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('NGQ_K[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());raw=(p.parent/'stdout.log').read_text()
 bad=any(s in raw for s in ['CBMC timed out','CBMC failed','Timed out','timed out. You may','unwinding assertion']) or r['exit_status']==124
 status='TOOL_LIMIT' if bad else 'PASS' if r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in raw else 'ASSERTION_FAILED' if 'VERIFICATION:- FAILED' in raw and 'Failed Checks: assertion failed:' in raw else 'PRE_VERIFICATION_FAILURE'
 failure=re.findall(r'Failed Checks: (.*)',raw)
 g=E/(p.parent.name+'-graph-check.json');lock=E/(p.parent.name+'-lock-check.json')
 graph=json.loads(g.read_text()) if g.exists() else None
 lockval=json.loads(lock.read_text()) if lock.exists() else None
 rows.append(dict(attempt=p.parent.name,target=r['module'],status=status,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],cgroup_peak_bytes=r.get('cgroup_memory_peak_bytes'),swaps=r['swaps'],failure=failure,graph_matches_frozen=graph and graph['graph_matches_frozen'],lock_unchanged=lockval and lockval['unchanged'],receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
by={r['attempt']:r for r in rows}
families=[('finish',4,5),('pair0',24,26)]+[(f'pair{k}',27+2*(k-1),28+2*(k-1)) for k in range(1,5)]+[(f'pair{k}',36+2*(k-5),37+2*(k-5)) for k in range(5,8)]+[('query_words',42,43),('post_membership_branch',45,60),('outer_scan_boundary',46,47),('default',48,49),('tail',50,51),('absorb',52,53),('initialization',54,55),('decoder_call_boundary',56,57),('range_iteration',58,59)]
selected=[]
for name,p,n in families:
 p=f'NGQ_K{p:03}';n=f'NGQ_K{n:03}';a=by.get(p);b=by.get(n)
 valid=bool(a and b and a['status']=='PASS' and b['status']=='ASSERTION_FAILED' and all(r['graph_matches_frozen'] and r['lock_unchanged'] for r in [a,b]))
 selected.append(dict(family=name,positive=p,negative=n,matched_fragment=valid,status='CHECKED_FRAGMENT' if valid else 'OPEN',composed_row_credit=False))
(E/'NGQ_NATIVE_RESULTS.json').write_text(json.dumps({'runs':rows,'selected':selected,'credit':'No fragment alone establishes TX1:168 or its chronological native producer'},indent=1)+'\n')
print(json.dumps({'runs':len(rows),'checked_fragments':sum(r['matched_fragment'] for r in selected),'open_fragments':[r['family'] for r in selected if not r['matched_fragment']]}))
