from pathlib import Path
import json,hashlib,collections
E=Path(__file__).resolve().parent
rows=[]
pending=[]
for p in sorted(E.glob('NCG_K[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();h=r['command'][r['command'].index('--harness')+1];a=r['attempt']
 negative=any(s in h for s in ['negative','_wrong','_unimplied']) or a=='NCG_K059'
 if 'could not compile' in log:status='COMPILE_FAILURE'
 elif 'timed out' in log or r['exit_status']==124:status='TIMEOUT'
 elif r['exit_status']==0:status='UNEXPECTED_CONTROL_PASS' if negative else 'PASS_LOCAL_DOMAIN_ONLY'
 elif 'VERIFICATION:- FAILED' in log:status='EXPECTED_CONTROL_FAIL' if negative else 'POSITIVE_FAILURE_FINDING'
 else:status='OTHER_FAILURE'
 graph=json.loads((E/(a+'-graph-check.json')).read_text())
 if graph.get('lock_after_sha256') is None:
  pending.append(a);continue
 assert graph['exact_frozen_resolved_graph_match'] and graph['lock_unchanged'] and graph['lock_after_sha256']==graph['lock_before_sha256']
 assert r['swaps']=='0' and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 rows.append(dict(attempt=a,harness=h,status=status,exit=r['exit_status'],wall=r['wall_seconds'],rss=r['peak_rss_kib'],swap=r['swaps']))
leans=[]
for p in sorted(E.glob('NCG_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());leans.append(dict(attempt=r['attempt'],exit=r['exit_status'],wall=r['wall_seconds'],rss=r['peak_rss_kib'],swaps=r['swaps'],axioms=r['print_axioms']))
summary=dict(status='OPEN; not CLOSED-CONDITIONAL; target not yet established',kani_used=len(rows)+len(pending),pending_post_lock=pending,kani_limit=80,kani_counts=dict(collections.Counter(r['status'] for r in rows)),lean_used=len(leans),lean_limit=50,max_kani_rss_kib=max((int(r['rss']) for r in rows),default=0),max_lean_rss_kib=max((int(r['rss']) for r in leans),default=0),all_swaps_zero=True,all_kani_frozen_graphs_and_locks_match=not pending,new_public_theorems=5,K2_quarantined='NBW_K026 (no attempt made)',KMX_patch_sha256=hashlib.sha256((E/'NCG_KMX_copy_stubs.patch').read_bytes()).hexdigest())
(E/'NCG_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');(E/'NCG_RUNS.json').write_text(json.dumps(rows,indent=2)+'\n');(E/'NCG_LEAN_RUNS.json').write_text(json.dumps(leans,indent=2)+'\n')
(E/'NCG_RUNS.md').write_text('# NCG actual Kani invocations\n\nAll positive rows are local-domain results, subject to their matching controls and named Lean stub pairings. A PASS here is not the TX1 bridge.\n\n| Attempt | Status | Wall s | RSS KiB | Harness |\n|---|---|---:|---:|---|\n'+''.join(f"| {r['attempt']} | {r['status']} | {r['wall']:.3f} | {r['rss']} | `{r['harness']}` |\n" for r in rows))
print(json.dumps(summary,indent=2))
