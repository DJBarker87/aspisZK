"""Strict local evidence validation; no prover or release replay."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(l) for l in (E/'NKP_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({x['attempt'] for x in receipts})==len(receipts)
by={x['attempt']:x for x in receipts}
idx=json.loads((E/'NKP_INPUTS.json').read_text());objects={}
for h,x in idx['objects'].items():
 raw=(E/x['path']).read_bytes();assert sha(raw)==x['archive_sha256'];data=lzma.decompress(raw);assert sha(data)==h and len(data)==x['bytes'];objects[h]=data
native=[];features=set();unused_flag_checks=0
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for x in receipts:
 assert x['limits']==limits and int(x['swaps'])==0,x['attempt']
 assert x['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-tx2-adapters2-20261108/NKP_target'
 a=x['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 disks=list(E.glob(a+'-disk-*.json'));assert disks and any(json.loads(p.read_text())['allowed'] for p in disks)
 if x['kind']=='lean':assert '-M7000' in x['command']
 if x['kind']!='kani':continue
 native.append(x);assert x['env']['CARGO_NET_OFFLINE']=='true'
 g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'];features.add(sha(json.dumps(g['all_features'],sort_keys=True).encode()))
 lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert json.loads((E/(a+'-erasure-check.json')).read_text())['passed']
 assert not json.loads((E/(a+'-source-check.json')).read_text())['errors']
 mapping=idx['attempts'][a]
 for n,h in mapping.items():
  if n.endswith('KMX_stubs.rs'):assert h=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
  if n.endswith('.rs'):assert b'NKP_invert' not in objects[h],('unused cfg body parity',a,n)
 unused_flag_checks+=1
assert len(native)==80 and len(features)==1
pairs=[]
for n in range(2,80,2):
 a,b=f'NKP_K{n:03}',f'NKP_K{n+1:03}'
 pa=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();pb=lzma.decompress((E/b/'stdout.log.xz').read_bytes()).decode()
 assert by[a]['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in pa
 assert by[b]['exit_status']!=0 and 'VERIFICATION:- FAILED' in pb and 'Failed Checks:' in pb and 'timed out' not in pb
 assert any(k in pb for k in ['actual wrapper returned field/error at SAME raw decoder call','lane constructor returned selected field','lane iteration exact bytes and reply','lane iteration selected write and error frame','lane iteration untouched coordinate','lane iteration guard exact Result','lane header ordered Result','lane zero-root ordered Result','registry ordered comparison stage exact Result'])
 fa=by[a]['env']['RUSTFLAGS'];fb=by[b]['env']['RUSTFLAGS'];assert fa==fb.replace(' --cfg NKP_invert','')
 pairs.append([a,b])
assert 'timed out' in lzma.decompress((E/'NKP_K001/stdout.log.xz').read_bytes()).decode()
assert by['NKP_K080']['exit_status']==0
# Raw ax2: every new root plus all NKF roots and headline; fixtures deliberately plant axioms.
raw=lzma.decompress((E/'NKP_L022/stdout.log.xz').read_bytes()).decode();rows=[json.loads(l.removeprefix('NEP_RESULT ')) for l in raw.splitlines() if l.startswith('NEP_RESULT ')]
expected=json.loads((E/'NKP_AUDIT_ROOTS.json').read_text())['groups'][0]
assert set(x['root'] for x in rows)==set(expected) and len(rows)==len(expected)==76
allowed={'propext','Classical.choice','Quot.sound'}
assert all(x['equal'] and set(x['walked_axioms'])<=allowed and sorted(x['walked_axioms'])==sorted(x['collect_axioms']) for x in rows)
fixture=lzma.decompress((E/'NKP_L008/stdout.log.xz').read_bytes()).decode();fs=[json.loads(l.removeprefix('NEP_RESULT ')) for l in fixture.splitlines() if l.startswith('NEP_RESULT ')]
assert len(fs)==8 and all(x['equal'] for x in fs)
assert sum(bool(set(x['walked_axioms'])-allowed) for x in fs)==4
# Exact source for every current theorem module must be a successful compile input.
mods=['NKP_BoxCuts','NKP_BoxUniformity','NKP_LaneCuts','NKP_LaneInduction','NKP_LaneCarrier','NKP_LaneCompletion','NKP_RegistryCuts']
for m in mods:
 h=sha((E/(m+'.lean')).read_bytes());assert any(x['module']==m and x['exit_status']==0 and h in x['source_hashes'].values() for x in receipts)
 s=(E/(m+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option max(?:RecDepth|Heartbeats)',s)
 for name in re.findall(r'^theorem (\w+)',s,re.M):assert '#print axioms '+name in s
scan=[]
with lzma.open(E/'NKP_LOADED_scan.jsonl.xz','rt') as f:
 for line in f:
  x=json.loads(line);assert x['imports_match'] and not x['dangling'] and not x['duplicate_owners'];scan.append(x)
pins=json.loads(lzma.decompress((E/'NKP_CLOSURE_PINS.json.xz').read_bytes()));assert pins['scan_pass'] and not pins['mismatches'] and pins['predecessor_files']==32817
for a in ['NKP_L021','NKP_L008','NKP_L022','NKP_L023','NKP_L024']:assert by[a]['exit_status']==0
assert not subprocess.check_output(['git','diff','--name-only','ce875f1b46f','--','crates','programs']).strip()
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
io=0
for p in E.glob('NKP_*/time.log.xz'):
 m=re.search(r'File system outputs:\s*(\d+)',lzma.decompress(p.read_bytes()).decode())
 if m:io+=int(m[1])*512
out=dict(status='PASS',kani_invocations=80,matched_pairs=len(pairs),excluded_timeout=['NKP_K001'],excluded_unpaired_positive=['NKP_K080'],quarantined_function_pointer=[],suspended_writable_static=[],source_objects=len(objects),all_crate_feature_fingerprints=len(features),kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',unused_cfg_flag_body_checks=unused_flag_checks,unused_cfg_note='Historical field inverse configs added --cfg NKP_invert; it occurs in zero Rust input bodies, features match, KMX bytes identical. Later controls use identical RUSTFLAGS. This is a body-identity check, no proof rerun.',raw_ax2_roots=len(rows),fixtures=len(fs),planted_detected=4,mutations_clear=4,all_equal_collectAxioms=True,NFX_modules=len(scan),predecessor_files=pins['predecessor_files'],selected_files=len(pins['selected_objects']),scope_filesystem_output_bytes=io,formal_support_scopes=sum(x['kind']!='kani' for x in receipts),wall_seconds=sum(x['wall_seconds'] for x in receipts),peak_rss_kib=max(int(x['peak_rss_kib']) for x in receipts),swaps=0,shipped_changes=False,combined_audits_used=2,combined_audits_limit=2)
(E/'NKP_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps({k:out[k] for k in ['status','kani_invocations','matched_pairs','raw_ax2_roots','NFX_modules','formal_support_scopes','peak_rss_kib']}))
