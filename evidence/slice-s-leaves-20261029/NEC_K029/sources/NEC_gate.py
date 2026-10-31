"""Own strict validation, executed inside the admitted capped scope before Kani."""
from pathlib import Path
import json,subprocess,sys,hashlib,tomllib,os
B=Path(__file__).resolve().parent;x=json.loads((B/sys.argv[1]).read_text());a=x['attempt'];S=B/'NEC_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(S/'Cargo.lock')==frozen,'STOP frozen lock mismatch before Kani'
kmx={'KMX_stubs.rs': 'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138', 'KMX_native.rs': 'cf719c47b5c8c91dcc369984c01bd0b8531b25210e344c9fd06db21b30171880', 'KMX_CopyMeaning.lean': '2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'}
for n,h in kmx.items():assert sha(S/n)==h,('KMX exact patch mismatch',n)
pins=json.loads((B/'NEC_SOURCE_PINS.json').read_text())
errors=[n for n,h in pins.items() if sha(S/n)!=h]
(B/(a+'-source-check.json')).write_text(json.dumps(dict(files=len(pins),errors=errors),indent=2)+'\n')
assert not errors,errors
r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1','--manifest-path',str(S/'programs/r1-cost-probe/Cargo.toml'),'--features','pool-adapter,private-leaf-salts'],cwd=S,capture_output=True,text=True)
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
visit(next(p['id'] for p in m['packages'] if p['name']=='aspis-r1-cost-probe-program'))
out=dict(graph_matches_frozen=not added and not(missing-allowed_missing) and not edge_errors,frozen_packages=len(f),resolved_packages=len(actual),new_package_tuples=sorted(added,key=str),missing_package_tuples=sorted(missing,key=str),edge_errors=edge_errors,lock_sha256=frozen,graph_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),selected_closure=[dict(name=pkgs[i]['name'],version=pkgs[i]['version'],source=pkgs[i].get('source'),features=nodes[i]['features']) for i in sorted(seen)])
(B/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n');assert out['graph_matches_frozen'],out
from NEC_graph import exact_graph
out.update(exact_graph(m,lock))
features={pkgs[i]['name']:nodes[i]['features'] for i in seen}
assert {'pool-adapter','private-leaf-salts'} <= set(features['aspis-r1-cost-probe-program'])
assert 'no-entrypoint' not in features['aspis-r1-cost-probe-program']
assert {'default','private-leaf-salts','optimized-terminal','program-build'} <= set(features['aspis-r1-cost-probe'])
assert {'r0','pool-v1-kernel'} <= set(features['aspis-statement'])
(B/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n')
assert sha(S/'Cargo.lock')==frozen,'STOP metadata changed lock'
out['resolved_features_all_crates']=[dict(name=p['name'],version=p['version'],source=p.get('source'),features=nodes[p['id']]['features']) for p in sorted(m['packages'],key=lambda p:p['id'])]
(B/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n')
# Validate and record the actual Kani target, in addition to deployed program context.
cmd=x['native_command'];manifest=cmd[cmd.index('--manifest-path')+1];selected=cmd[cmd.index('--features')+1]
r2=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1','--manifest-path',manifest,'--features',selected],cwd=S,capture_output=True,text=True)
(B/(a+'-actual-graph.stderr')).write_text(r2.stderr)
assert r2.returncode==0,r2.stderr
actual_metadata=json.loads(next(l for l in r2.stdout.splitlines() if l.startswith('{')))
actual_nodes={n['id']:n for n in actual_metadata['resolve']['nodes']}
actual_features={p['name']:actual_nodes[p['id']]['features'] for p in actual_metadata['packages']}
actual_check=exact_graph(actual_metadata,lock)
for reached in ['aspis-statement','aspis-core']:
 assert actual_features[reached]==features[reached],('reached target feature mismatch',reached,actual_features[reached],features[reached])
actual_check.update(resolved_features_all_crates=[dict(name=p['name'],version=p['version'],source=p.get('source'),features=actual_nodes[p['id']]['features']) for p in sorted(actual_metadata['packages'],key=lambda p:p['id'])],native_manifest=manifest,native_features=selected,deployed_reached_feature_parity=['aspis-statement','aspis-core'],helper_reason='Target is the statement wrapper only; no verifier library/program bodies are compiled into the selected proof. Exact deployed statement/core features are selected explicitly.')
(B/(a+'-actual-graph-check.json')).write_text(json.dumps(actual_check,indent=1)+'\n')
assert sha(S/'Cargo.lock')==frozen,'STOP actual metadata changed lock'
version=subprocess.run([x['native_command'][0],'kani','--version'],capture_output=True,text=True)
assert version.returncode==0 and '0.67.0' in version.stdout,(version.returncode,version.stdout,version.stderr)
tool_files=[Path(x['native_command'][0])]
for root in [Path('/home/dombarker/.kani/kani-0.67.0/bin'),Path('/home/dombarker/.local/share/kani/0.67.0/bin')]:
 if root.exists():tool_files.extend(p for p in root.iterdir() if p.is_file())
(B/(a+'-tool-pins.json')).write_text(json.dumps(dict(version=version.stdout.strip(),tools={str(p):dict(sha256=sha(p),bytes=p.stat().st_size,realpath=str(p.resolve())) for p in tool_files}),indent=1)+'\n')
if x.get('trace_source_attempt'):
 from NEC_trace import run_trace
 status=run_trace(B,x,tool_files)
else:status=subprocess.run(x['native_command'],cwd=B).returncode
target=Path(x['native_command'][x['native_command'].index('--target-dir')+1]);base_name=x['module'].split('::')[-1]
artifacts={str(p):dict(sha256=sha(p),bytes=p.stat().st_size) for p in target.rglob('*') if p.is_file() and (base_name in p.name or p.name.endswith('.kani-metadata.json'))}
(B/(a+'-native-pins.json')).write_text(json.dumps(artifacts,indent=1)+'\n')
last=sha(S/'Cargo.lock');(B/(a+'-lock-check.json')).write_text(json.dumps(dict(before=frozen,after=last,unchanged=last==frozen),indent=2)+'\n');assert last==frozen,'STOP Kani changed lock'
sys.exit(status)
