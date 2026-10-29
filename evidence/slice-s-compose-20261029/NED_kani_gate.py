"""Lane-owned strict frozen graph/source gate, inside the capped scope."""
from pathlib import Path
import subprocess,json,hashlib,tomllib,sys
B=Path(__file__).resolve().parent;cfg=json.loads((B/sys.argv[1]).read_text());a=cfg['attempt'];S=B/'NED_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock_hash='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(S/'Cargo.lock')==lock_hash,'STOP frozen lock mismatch'
patch=B/'NED_KMX_copy_stubs.patch';assert sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
for n,h in {'KMX_stubs.rs':'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138','KMX_native.rs':'cf719c47b5c8c91dcc369984c01bd0b8531b25210e344c9fd06db21b30171880','KMX_CopyMeaning.lean':'2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'}.items():assert sha(S/n)==h,('KMX file mismatch',n)
pins=json.loads((B/'NED_RUST_SHA256.json').read_text());errors=[n for n,h in pins.items() if sha(S/n)!=h]
(B/(a+'-source-check.json')).write_text(json.dumps(dict(files=len(pins),errors=errors),indent=1)+'\n');assert not errors,errors
cmd=['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',str(S/'crates/aspis-statement/Cargo.toml'),'--locked','--offline','--format-version','1','--features',cfg['statement_features']]
r=subprocess.run(cmd,cwd=S,capture_output=True,text=True);(B/(a+'-metadata.stderr')).write_text(r.stderr)
assert r.returncode==0,r.stderr
metadata=json.loads(next(l for l in r.stdout.splitlines() if l.startswith('{') and '"packages"' in l))
(B/(a+'-metadata-pin.json')).write_text(json.dumps(dict(command=cmd,sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),bytes=len(r.stdout.encode()),features_all_crates=[dict(name=p['name'],version=p['version'],features=next(n['features'] for n in metadata['resolve']['nodes'] if n['id']==p['id'])) for p in metadata['packages']]),indent=1)+'\n')
version=subprocess.run(['/home/dombarker/.cargo/bin/cargo-kani','--version'],capture_output=True,text=True)
assert version.returncode==0 and '0.67.0' in version.stdout,(version.returncode,version.stdout,version.stderr)
(B/(a+'-tools.json')).write_text(json.dumps(dict(cargo_kani_version=version.stdout.strip(),cargo_kani_sha256=sha(Path('/home/dombarker/.cargo/bin/cargo-kani'))),indent=1)+'\n')
locked=tomllib.loads((S/'Cargo.lock').read_text());key=lambda p:(p['name'],p['version'],p.get('source'))
frozen={key(p):p for p in locked['package']};actual={key(p):p for p in metadata['packages']};nodes={n['id']:n for n in metadata['resolve']['nodes']};packages={p['id']:p for p in metadata['packages']}
added=set(actual)-set(frozen);missing=set(frozen)-set(actual);allowed_missing={('aspis-r1-cert-build','0.0.0',None),('aspis-r1-cert-check','0.0.0',None),('aspis-z4b-probe','0.1.0',None)}
edge_errors=[]
for p in metadata['packages']:
 for dep in nodes[p['id']]['dependencies']:
  q=packages[dep];ok=False
  for label in frozen[key(p)].get('dependencies',[]):
   parts=label.split(' ')
   if len(parts)==1 and sum(k[0]==q['name'] for k in frozen)>1:continue
   if parts[0]==q['name'] and (len(parts)<2 or parts[1]==q['version']) and (len(parts)<3 or parts[2].strip('()')==q.get('source')):ok=True
  if not ok:edge_errors.append([key(p),key(q)])
normalized=dict(packages=sorted(json.dumps(list(key(p)),separators=(',',':')) for p in metadata['packages']),edges=sorted([json.dumps(list(key(p)),separators=(',',':')),sorted(json.dumps(list(key(packages[d])),separators=(',',':')) for d in nodes[p['id']]['dependencies'])] for p in metadata['packages']))
expected=json.loads((B/'NED_FROZEN_GRAPH.json').read_text())
check=dict(graph_matches_frozen=not added and not(missing-allowed_missing) and not edge_errors,exact_LPm_graph=normalized==expected,added=sorted(added,key=str),missing=sorted(missing,key=str),edge_errors=edge_errors,lock_sha256=lock_hash,normalized_sha256=hashlib.sha256(json.dumps(normalized,sort_keys=True).encode()).hexdigest(),all_crates_recorded=len(metadata['packages']),cfg_if_libc=[key(p) for p in metadata['packages'] if p['name'] in ['cfg-if','libc']])
(B/(a+'-graph-check.json')).write_text(json.dumps(check,indent=1)+'\n');assert check['graph_matches_frozen'] and check['exact_LPm_graph'],check
assert sha(S/'Cargo.lock')==lock_hash,'STOP metadata changed lock'
# Record explicit deployed statement feature closure; controls reach only the
# feature-independent PaymentError declaration and these new scratch bodies.
features=next(n['features'] for n in metadata['resolve']['nodes'] if packages[n['id']]['name']=='aspis-statement')
assert set(cfg['required_statement_features'])<=set(features),(features,cfg['required_statement_features'])
status=subprocess.run(cfg['native_command'],cwd=B).returncode if cfg['kind']=='kani' else 0
last=sha(S/'Cargo.lock');(B/(a+'-lock-check.json')).write_text(json.dumps(dict(before=lock_hash,after=last,unchanged=last==lock_hash),indent=1)+'\n');assert last==lock_hash,'STOP Kani changed lock'
sys.exit(status)
