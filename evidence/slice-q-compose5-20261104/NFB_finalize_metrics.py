from pathlib import Path
import json,collections,hashlib,subprocess,re
E=Path(__file__).resolve().parent
rows=[json.loads(p.read_text()) for p in sorted(E.glob('NFB_*/receipt.json'))]
counts=collections.Counter(r['kind'] for r in rows)
assert counts==dict(kani=110,lean=90,extract=1),counts
for r in rows:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 assert r['source_revision'] and r['source_hashes'] and float(r['wall_seconds'])>0
metrics=[{k:r.get(k) for k in ['attempt','kind','module','target','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','print_axioms','limits']} for r in rows]
(E/'NFB_METRICS.json').write_text(json.dumps(metrics,indent=1)+'\n')
(E/'NFB_BUDGET.json').write_text(json.dumps(dict(limits=dict(kani=110,lean=90,extract=10),executed=dict(counts),unused_extractions=9,reason='Actual row/root source forests already exist; extraction cannot discharge remaining native same-receiver/frame joins, callee boundary packets or audit admission. Both primary budgets exhausted; no additional formal scope authorized.',keys_touched=False,pushed=False),indent=1)+'\n')
print(json.dumps(dict(executed=dict(counts),swaps=0,security_target_established=False)))
