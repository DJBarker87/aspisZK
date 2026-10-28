from pathlib import Path
import json,re,hashlib,collections
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('NBO_[KLG]*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt']
 rows.append({k:r.get(k) for k in ['attempt','kind','module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_tree_dirty','source_hashes','deps_fingerprint','limits','cgroup_memory_peak_bytes','print_axioms']})
(E/'NBO_RUN_LEDGER.json').write_text(json.dumps(rows,indent=2)+'\n')
kani=[r for r in rows if r['kind']=='kani'];lean=[r for r in rows if r['kind']=='lean']
assert len(kani)==40 and len(lean)<100
for r in kani:
 a=r['attempt'];g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['exact_frozen_resolved_graph_match'] and g['lock_unchanged']
 assert g['lock_before_sha256']==g['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
for r in rows:
 assert r['swaps']=='0'
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
audit=json.loads((E/'NBO_L044/receipt.json').read_text());assert audit['exit_status']==0
names=json.loads((E/'NBO_THEOREMS.json').read_text());assert len(names)==49
axioms=audit['print_axioms'];assert len(axioms)==49
for n,line in zip(names,axioms):
 assert "'"+n+"'" in line
 assert 'sorryAx' not in line
 if 'depends on axioms:' in line:
  assert set(re.search(r'\[([^]]*)\]',line).group(1).split(', '))<={'propext','Classical.choice','Quot.sound'}
for r in kani:
 pin=json.loads((E/'NBO_NATIVE_SOURCES.json').read_text())[r['attempt']]
 assert pin['harness_sha256']==r['source_hashes']['NBO_src/crates/aspis-r1-cost-probe/src/NBO_native.rs']
summary=dict(kani_runs=len(kani),kani_raw_exit0=sum(r['exit_status']==0 for r in kani),kani_compliant_local_passes=sum(r['exit_status']==0 and r['attempt']!='NBO_K001' for r in kani),excluded_overlap='NBO_K001; NBO_L002 failed',kani_nonzero=[r['attempt'] for r in kani if r['exit_status']!=0],lean_compile_processes=len(lean),lean_slots=44,preflight_only='NBO_L021',lean_successes=sum(r['exit_status']==0 for r in lean),public_theorems_audited=49,new_proof_modules=25,audit='NBO_L044',standard_axioms_only=True,all_40_frozen_graph_and_lock_checks=True,max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),all_swap_zero=True,kani_budget_exhausted=True,memory_copy_credit="HELD pending KDX_; exit0 counts are not closure credit")
(E/'NBO_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
