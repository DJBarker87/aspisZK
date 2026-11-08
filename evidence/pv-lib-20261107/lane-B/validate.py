"""Validate bounded session evidence, source pins, assignments, and write scope."""
import collections,hashlib,json,lzma,pathlib,re,subprocess
E=pathlib.Path('evidence/pv-lib-20261107/lane-B');M='fbc60bd811d36ca79d71aabc563f709c26b9d2da'
manifest=json.loads((E/'AUDIT_ROOTS.json').read_text());results=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert 56400<=a<=56499
 turn=json.loads((E/f'turn-{a}.json').read_text());admit=json.loads((E/f'admission-{a}.json').read_text())
 assert turn['exit']==0 and admit['allowed'] is True
 assert all(flag in r['command'] for flag in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert r['exit'] is not None and r['wall'] and int(r['peak_rss_kbytes'])<8*1024*1024 and int(r['swaps'])==0
 assert r['source_revision'] and r['source_sha256']
 if r['accepted']:
  assert r['exit']=='0' and r['launcher_exit']==0
  src=pathlib.Path(r['source_path']);assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256']
  if not r['runtime_audit']:
   log=(E/f'out-{a}.log').read_text();assert 'sorryAx' not in log and 'error:' not in log
   assert r['axioms_summary_based']
 else:
  failed=E/f'failed-input-{a}.lean.xz';assert failed.exists()
  assert hashlib.sha256(lzma.decompress(failed.read_bytes())).hexdigest()==r['source_sha256']
 results.append({k:r.get(k) for k in ['attempt','target','runtime_audit','accepted','exit','wall','peak_rss_kbytes','swaps','source_revision','source_sha256','axioms_summary_based']})
delta=json.loads((E/'MAP-DELTA-S5.json').read_text());assert len(delta['slots'])==60
assert dict(collections.Counter(s['status'] for s in delta['slots']))=={'INSTANTIATED':16,'WAITING-ON-ROW':39,'CORRECTED-STATEMENT':5}
for s in delta['slots']:
 if s['status']=='WAITING-ON-ROW':assert s['waiting_on_row'] and s['proof_attempted'] is False
 if s['status']=='INSTANTIATED':assert s['compiled'] and s['caller_domain'] and s['theorem'] and s['graph_of_function']
for m in manifest['modules']:
 src=pathlib.Path('lean',m+'.lean').read_text()
 assert set(re.findall(r'^theorem (\w+)',src,re.M)) <= set(re.findall(r'^#print axioms (\w+)',src,re.M))
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',src)
paths=subprocess.check_output(['git','diff','--name-only',M],text=True).splitlines()
assert all(p.startswith('lean/PV_LIB_B_') or p.startswith(str(E)+'/') for p in paths),paths
for f in E.rglob('*'):
 if f.is_file():assert f.stat().st_size<20*1024*1024,f
# Shared artifacts are byte-identical to the one allowed merge.
for p in ['evidence/pv-lib-20261107/PLIB_MAP.md','evidence/pv-lib-20261107/PLIB_MAP.json']:
 assert pathlib.Path(p).read_bytes()==subprocess.check_output(['git','show',M+':'+p])
summary=dict(focused_passes=sum(r['accepted'] and not r['runtime_audit'] for r in results),failed_compiles=[r['attempt'] for r in results if not r['accepted']],preflight_refusals=[56416],raw_audit_scopes=[r['attempt'] for r in results if r['runtime_audit']],peak_rss_kbytes=max(int(r['peak_rss_kbytes']) for r in results),swaps=0,changed_paths=paths,manifest_root_count=len(manifest['roots']),receipts=results,shared_map_unchanged=True,only_assigned_worktree=True,ledger_and_other_lanes_unchanged=True)
(E/'VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print({k:v for k,v in summary.items() if k not in ['changed_paths','receipts']})
