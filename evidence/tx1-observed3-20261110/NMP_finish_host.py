"""Final bounded evidence checks; no theorem or native proof replay."""
from pathlib import Path
import json,lzma,hashlib,sys,shutil,re
B=Path.cwd();mode=sys.argv[1];H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(B/n).write_text(json.dumps(x,indent=1)+'\n')
if mode=='native':
 sources=json.loads((B/'NMP_SOURCE_PINS.json').read_text());assert all(H(B/'NMP_src'/n)==h for n,h in sources.items())
 assert H(B/'NMP_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert H(B/'NMP_KMX.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 rows=[]
 for p in sorted(B.glob('NMP_K[0-9][0-9][0-9]/receipt.json')):
  a=p.parent.name;rc=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();graph=json.loads((B/(a+'-graph-check.json')).read_text());lock=json.loads((B/(a+'-lock-check.json')).read_text());assert graph['graph_matches_frozen']and lock['unchanged'],a
  baseline=B/(a+'-baseline-check.json');base=json.loads(baseline.read_text())if baseline.exists()else None
  if base:assert not base['errors'],a
  verdict='PASS'if rc['exit_status']==0 and'VERIFICATION:- SUCCESSFUL'in log else'TIMEOUT'if'CBMC timed out'in log or rc['exit_status']==124 else'COMPILE_FAILURE'if'could not compile'in log else'NEGATIVE_OR_FAILED_CHECK'
  rows.append(dict(attempt=a,module=rc['module'],exit=rc['exit_status'],verdict=verdict,wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'],source_manifest_sha256=H(p.parent/'sources/NMP_SOURCE_PINS.json'),baseline=base))
 assert len(rows)==100,len(rows)
 scan=[]
 for n in sources:
  if '/NMP_'not in n:continue
  txt=(B/'NMP_src'/n).read_text()
  assert not re.search(r'\bstatic\s+mut\b',txt),n
  scan.append(n)
 out=dict(status='RETAINED_LOCAL_NATIVE_SUPPORT_ONLY',runs=rows,native_parent_realization=False,closed_rows=[],full_prefix_type_coverage=False,full_resource_packets=False,scanned_own_modules=scan,writable_static_suspended=[],option_fn_quarantine='None-path evidence requires the recorded same-configuration stability pair; no function-pointer value assertion',KMX_patch_sha256=H(B/'NMP_KMX.patch'),allocator_std_trust='retained, never removed',new_trust_rows=[])
 write('NMP_NATIVE_FINAL.json',out)
elif mode=='retention':
 count=0
 for p in(B/'NMP_audit').rglob('*.xz'):
  raw=lzma.decompress(p.read_bytes());q=Path(str(p)[:-3]+'.sha256');assert q.is_file()and hashlib.sha256(raw).hexdigest()==q.read_text().strip(),str(p);count+=1
 for name in ['NMP_CLOSURE_PINS.json.xz','NMP_NLZ_CLOSURE_PINS.json.xz','NMP_NLX_CLOSURE_PINS.json.xz']:
  x=json.loads(lzma.decompress((B/name).read_bytes()))
  # Predecessor manifests name original paths. Compare the copied resolution in
  # closure comparison; do not read/write a sibling worktree or mutate a cache.
  if name=='NMP_CLOSURE_PINS.json.xz':
   for r in x['selected_objects']:assert H(Path(r['path']))==r['sha256'],r['path']
 own=sum(p.stat().st_size for p in B.rglob('*')if p.is_file());assert own<30_000_000_000
 out=dict(status='PASS',compressed_sha_pairs=count,own_host_bytes=own,disk=shutil.disk_usage(B)._asdict(),deletions=0,cache_retained=True)
 write('NMP_RETENTION.json',out)
elif mode=='audit':
 expected=json.loads((B/'NMP_AUDIT_ROOTS.json').read_text());roots=[];mismatches=[];groups=[]
 for j in range(len(expected['groups'])):
  r=json.loads((B/'NMP_audit'/('proof'+str(j))/('proof'+str(j)+'.json')).read_text());assert r['exit_status']==0;groups.append({k:v for k,v in r.items()if k not in ['results','print_axioms']})
  for v in r['results']:
   assert set(v['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},v
   roots.append(v['root'])
   if not v['equal']:mismatches.append(v)
 assert sorted(roots)==sorted(expected['roots']),'Missing/repeated raw roots'
 scan=[json.loads(l)for l in(B/'NMP_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
 fixture=json.loads((B/'NMP_audit/fixtures/fixtures.json').read_text());assert len(fixture['results'])==8 and all(r['equal']for r in fixture['results'])
 comparison=json.loads((B/'NMP_PREDECESSOR_COMPARISON.json').read_text());assert all(r['status']=='PASS'for r in comparison.values())
 for r in json.loads((B/'NMP_EXPORT.json').read_text())['files']:assert H(Path(r['path']))==r['sha256']
 out=dict(status='PASS_STANDARD_RAW_WITH_RETAINED_COLLECTOR_DISAGREEMENTS'if mismatches else'PASS',target_established=False,headline='AspisR1.RPx_Deployed.deployed',combined_audits=1,scan_modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,raw_roots=len(roots),raw_groups=groups,raw_all_standard=True,collector_disagreements=mismatches,fixtures=fixture,predecessor_comparison=comparison,closed_rows=[],qualified_rows=[],full_resource_packets=False,retention=json.loads((B/'NMP_RETENTION.json').read_text()),native_status=json.loads((B/'NMP_NATIVE_FINAL.json').read_text())['status'])
 write('NMP_AUDIT.json',out)
else:raise AssertionError(mode)
print(json.dumps(dict(mode=mode,status=out['status'],target_established=False)))
