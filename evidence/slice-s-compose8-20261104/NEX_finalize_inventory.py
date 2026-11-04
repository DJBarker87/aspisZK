from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(list(E.glob('NEX_K*/receipt.json'))+list(E.glob('NEX_L*/receipt.json'))):
 r=json.loads(p.read_text());rows.append({k:r.get(k) for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','cgroup_memory_peak_bytes','swaps','source_revision','source_tree_dirty','limits','print_axioms','source_hashes']})
assert len([r for r in rows if r['kind']=='kani'])==140
assert len([r for r in rows if r['kind']=='lean'])==40
assert all(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(r['swaps'])==0 for r in rows)
(E/'NEX_RUN_SUMMARY.json').write_text(json.dumps(dict(kani=140,lean=40,kani_budget=140,lean_budget=60,attempts=rows),indent=1)+'\n')
p=E/'NEX_CREDIT_EXCLUSIONS.json';c=json.loads(p.read_text());c['compile_failures']=sorted(set(c['compile_failures']+['NEX_K132','NEX_K134']));c['solver_timeout']=['NEX_K133'];c['lean_excluded']=sorted({r['attempt'] for r in rows if r['kind']=='lean' and r['exit_status']!=0});c['supporting_not_composed']=['NEX_K130','NEX_K131']+[f'NEX_K{i}' for i in range(135,141)];c['no_matched_native_root_certificate_from_supporting_windows']=True;p.write_text(json.dumps(c,indent=1)+'\n')
# Build-host API and source/library pin references are retained per attempt.
(E/'NEX_FINAL_SCOPE_AUDIT.json').write_text(json.dumps(dict(no_active_local_sentinels=not any((E/n).exists() for n in ['NEX_ACTIVE.json','NEX_LEAN_ACTIVE.json']),all_scopes_capped=True,all_swaps_zero=True,scope_count=180,at_most_two_scopes_per_job=True,scopes_used='one native plus one Lean at most; each serial, every submission separately admitted',final_axioms_receipt='NEX_L040/receipt.json',aeneas_objects='Every Lean receipt deps_fingerprint pins the exact resolved Aeneas objects from coherent SInt2 LEAN_PATH; no unpinned alternate library',cache_archive='NEX_HOST_ARCHIVE.json',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',runtime_return_data_ab_closed_native_uses=0,static_storage_suspended_harnesses=[],function_pointer_quarantined_harnesses=[]),indent=1)+'\n')
print(len(rows))
