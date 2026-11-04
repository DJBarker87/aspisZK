from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
patch=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
pos={1,3,5,7,9,11,13,15,17,19,22,24};out=[]
for i in range(1,26):
 a=f'NFC_K{i:03}';r=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph-check.json')).read_text());l=json.loads((E/(a+'-lock-check.json')).read_text());s=json.loads((E/(a+'-rule16-check.json')).read_text());f=json.loads((E/(a+'-frozen-source-check.json')).read_text());log=(E/a/'stdout.log').read_text()
 assert g['graph_matches_frozen'] and g['exact_frozen_selected_graph'] and l['unchanged'] and not s['static_declarations'] and f['passed']
 assert r['env']['CARGO_NET_OFFLINE']=='true' and '--locked' not in r['native_command'] and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if i==21:assert 'CBMC timed out' in log;verdict='TIMEOUT_EXCLUDED'
 else:
  assert r['exit_status']==(0 if i in pos else 1)
  assert 'VERIFICATION:- '+('SUCCESSFUL' if i in pos else 'FAILED') in log and 'timed out' not in log
  verdict='PASS_LOCAL_WINDOW' if i in pos else 'MATCHED_CONTROL_FAIL'
 out.append(dict(attempt=a,module=r['module'],verdict=verdict,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_hashes=r['source_hashes'],cgroup_memory_peak_bytes=r.get('cgroup_memory_peak_bytes'),graph_pin=sha(E/(a+'-graph-check.json')),print_axioms='N/A: Kani; Lean counterparts in LPh_STUBS.md'))
for positive,negative,copy_ok,copy_bad in [(1,2,3,4),(5,6,15,16),(7,8,15,16),(9,10,15,16),(11,12,15,16),(13,14,15,16),(17,18,19,20),(22,23,24,25)]:
 r=[json.loads((E/f'NFC_K{i:03}'/'receipt.json').read_text()) for i in [positive,negative,copy_ok,copy_bad]]
 def payload(x):return {k:v for k,v in x['source_hashes'].items() if k.startswith('NFC_src/')}
 assert all(payload(x)==payload(r[0]) for x in r),[positive,negative,copy_ok,copy_bad]
(E/'NFC_NATIVE_AUDIT.json').write_text(json.dumps(dict(copy_patch_sha256=sha(patch),runs=out,groups=8,positive_windows=8,kani_total=25,timeout_excluded=['NFC_K021'],quarantined_function_pointer_harnesses=[],suspended_writable_static_harnesses=[],qualification='Local source/call-context windows only. Full parent and headline certificates remain OPEN.'),indent=2)+'\n')
print('PASS: 25 native receipts; 8 paired window groups; exact KMX, frozen graphs, deployed features and unchanged locks')
