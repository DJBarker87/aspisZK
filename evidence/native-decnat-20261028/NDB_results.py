from pathlib import Path
import json,re,hashlib,collections
E=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (E/'NDB_ATTEMPTS.jsonl').read_text().splitlines()]
groups=collections.defaultdict(list)
for r in rows:
 if r['kind']!='kani':continue
 a=r['attempt'];out=(E/a/'stdout.log').read_text();g=json.loads((E/(a+'-graph.json')).read_text());cfg=json.loads((E/(a+'.json')).read_text())
 assert g['graph_matches_frozen'] and g['lock_unchanged'] and g['offline']
 assert g['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert cfg['env']['CARGO_NET_OFFLINE']=='true'
 assert cfg['command'][-1]==r['module']
 status='excluded'
 if r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in out:status='positive'
 elif r['exit_status']==1 and 'Failed Checks: "NDB semantic law"' in out and 'unwinding assertion' not in out:status='intended_negative'
 elif 'unwinding assertion' in out:status='unwind_failure'
 elif a=='NDB_K014':status='stopped_stalled_negative'
 elif 'could not compile' in out:status='compile_failure'
 groups[r['module']].append(dict(attempt=a,status=status,exit=r['exit_status'],wall=r['wall_seconds'],rss=r['peak_rss_kib']))
result={n:dict(attempts=rs,paired_local_credit=any(r['status']=='positive' for r in rs) and any(r['status']=='intended_negative' for r in rs)) for n,rs in groups.items()}
x=dict(budget={'kani_used':sum(r['kind']=='kani' for r in rows),'lean_used':sum(r['kind']=='lean' for r in rows)},native_status_counts=dict(collections.Counter(r['status'] for rs in groups.values() for r in rs)),paired_local_components=sum(x['paired_local_credit'] for x in result.values()),groups=result,top_decoder_bridges={'op48':'OPEN','op49':'OPEN','op50':'OPEN'})
(E/'NDB_RESULTS.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:v for k,v in x.items() if k!='groups'},indent=2))
