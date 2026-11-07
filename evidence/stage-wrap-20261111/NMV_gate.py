"""Own strict validation, executed inside the admitted capped scope before Kani."""
from pathlib import Path
import json,subprocess,sys,hashlib,tomllib,os,re
B=Path(__file__).resolve().parent;x=json.loads((B/sys.argv[1]).read_text());a=x['attempt'];S=B/'NMV_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(S/'Cargo.lock')==frozen,'STOP frozen lock mismatch before Kani'
kmx={'KMX_stubs.rs': 'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138', 'KMX_native.rs': 'cf719c47b5c8c91dcc369984c01bd0b8531b25210e344c9fd06db21b30171880', 'KMX_CopyMeaning.lean': '2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'}
for n,h in kmx.items():assert sha(S/n)==h,('KMX exact patch mismatch',n)
pins=json.loads((B/'NMV_FROZEN_PINS.json').read_text());pins.update(json.loads((B/'NMV_EXTRA_PINS.json').read_text()));errors=[]
for n,h in pins.items():
 raw=(S/n).read_bytes()
 overlay=B/'NMV_source_overlays.json'
 if overlay.exists():
  for line in json.loads(overlay.read_text()).get(n,[]):
   assert (line.startswith('#[cfg_attr(kani,') or re.fullmatch(r'\n#\[cfg\(kani\)\]\n#\[path="NMV_[A-Za-z0-9_.]+"\]\nmod [A-Za-z0-9_]+;\n',line)) and raw.count(line.encode())==1,('invalid cfg-only overlay',n,line)
   raw=raw.replace(line.encode(),b'',1)
 if n=='crates/aspis-r1-cost-probe/src/lib.rs' and raw.startswith(b'#![cfg_attr(kani,feature(allocator_api))]\n'):
  prefix=b'#![cfg_attr(kani,feature(allocator_api))]\n'
  assert raw.startswith(prefix);raw=raw[len(prefix):]
 if n=='crates/aspis-r1-cost-probe/src/candidate.rs' and raw.endswith(b'\n#[cfg(kani)]\n#[path="NMV_native.rs"]\nmod NMV_native;\n'):
  suffix=b'\n#[cfg(kani)]\n#[path="NMV_native.rs"]\nmod NMV_native;\n'
  assert raw.endswith(suffix);raw=raw[:-len(suffix)]
 if n=='programs/r1-cost-probe/src/lib.rs' and raw.startswith(b'#![cfg_attr(kani,feature(allocator_api))]\n'):
  prefix=b'#![cfg_attr(kani,feature(allocator_api))]\n'
  assert raw.startswith(prefix);raw=raw[len(prefix):]
 if n=='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs' and raw.endswith(b'\n#[cfg(kani)]\n#[path="NMV_program.rs"]\nmod NMV_program;\n'):
  suffix=b'\n#[cfg(kani)]\n#[path="NMV_program.rs"]\nmod NMV_program;\n'
  assert raw.endswith(suffix);raw=raw[:-len(suffix)]
 if hashlib.sha256(raw).hexdigest()!=h:errors.append(n)
(B/(a+'-source-check.json')).write_text(json.dumps(dict(files=len(pins),errors=errors),indent=2)+'\n')
assert not errors,errors
assert os.environ['CARGO_NET_OFFLINE']=='true'
assert Path(os.environ['CARGO_TARGET_DIR'])==B/'NMV_target'
assert not (B/'NMV_target').is_symlink()
assert (B/'NMV_KMX_copy_stubs.patch').read_bytes()==(B/'NMV_expected_KMX.patch').read_bytes()
features=x['metadata_features'] if 'metadata_features' in x else 'aspis-core/r0' if x.get('root_package')=='aspis-core' else 'aspis-r1-cost-probe-program/pool-adapter,aspis-r1-cost-probe-program/private-leaf-salts' if x.get('root_package')=='aspis-r1-cost-probe-program' else 'aspis-r1-cost-probe/optimized-terminal,aspis-r1-cost-probe/program-build,aspis-r1-cost-probe/private-leaf-salts'
meta=['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1','--features',features]
if x.get('metadata_manifest'):meta+=['--manifest-path',x['metadata_manifest']]
r=subprocess.run(meta,cwd=S,capture_output=True,text=True)
(B/(a+'-graph.stderr')).write_text(r.stderr)
assert r.returncode==0,r.stderr
m=json.loads(next(l for l in r.stdout.splitlines() if l.startswith('{')))
lock=tomllib.loads((S/'Cargo.lock').read_text());key=lambda p:(p['name'],p['version'],p.get('source'))
f={key(p):p for p in lock['package']};actual={key(p):p for p in m['packages']};nodes={p['id']:p for p in m['resolve']['nodes']};pkgs={p['id']:p for p in m['packages']}
added=set(actual)-set(f);missing=set(f)-set(actual)
allowed_missing={('aspis-r1-cert-build','0.0.0',None),('aspis-r1-cert-check','0.0.0',None),('aspis-z4b-probe','0.1.0',None)}
edge_errors=[]
for p in m['packages']:
 for d in nodes[p['id']]['dependencies']:
  q=pkgs[d];ok=False
  for label in f[key(p)].get('dependencies',[]):
   v=label.split(' ')
   if len(v)==1 and sum(k[0]==q['name'] for k in f)>1:continue
   if v[0]==q['name'] and (len(v)<2 or v[1]==q['version']) and (len(v)<3 or v[2].strip('()')==q.get('source')):ok=True
  if not ok:edge_errors.append([key(p),key(q)])
seen=set()
def visit(i):
 if i in seen:return
 seen.add(i)
 for d in nodes[i]['dependencies']:visit(d)
visit(next(p['id'] for p in m['packages'] if p['name']==x.get('root_package','aspis-r1-cost-probe')))
out=dict(graph_matches_frozen=not added and not(missing-allowed_missing) and not edge_errors,frozen_packages=len(f),resolved_packages=len(actual),new_package_tuples=sorted(added,key=str),missing_package_tuples=sorted(missing,key=str),edge_errors=edge_errors,lock_sha256=frozen,graph_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),selected_closure=[dict(name=pkgs[i]['name'],version=pkgs[i]['version'],source=pkgs[i].get('source'),features=nodes[i]['features']) for i in sorted(seen)])
out['all_crate_features']=[dict(name=p['name'],version=p['version'],source=p.get('source'),features=nodes[p['id']]['features']) for p in m['packages']]
(B/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n');assert out['graph_matches_frozen'],out
assert sha(S/'Cargo.lock')==frozen,'STOP metadata changed lock'
(B/(a+'-kani-submitted.json')).write_text(json.dumps({'command':x['native_command'],'offline':os.environ['CARGO_NET_OFFLINE']})+'\n')
status=subprocess.run(['/usr/bin/timeout','--signal=TERM','--kill-after=5s','90s',*x['native_command']],cwd=B).returncode
last=sha(S/'Cargo.lock');(B/(a+'-lock-check.json')).write_text(json.dumps(dict(before=frozen,after=last,unchanged=last==frozen),indent=2)+'\n');assert last==frozen,'STOP Kani changed lock'
sys.exit(status)
