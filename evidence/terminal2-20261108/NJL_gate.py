"""Own strict validation, executed inside the admitted capped scope before Kani."""
from pathlib import Path
import json,subprocess,sys,hashlib,tomllib,os,base64,re
B=Path(__file__).resolve().parent;x=json.loads((B/sys.argv[1]).read_text());a=x['attempt'];S=B/'NJL_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Own-input repair: frozen literal-path closure omitted by original manifest.
for n,v in json.loads((B/'NJL_EXTRA_INPUTS.json').read_text()).items():
 p=S/n;raw=base64.b64decode(v,validate=True);p.parent.mkdir(parents=True,exist_ok=True)
 if not p.exists():p.write_bytes(raw)
 assert p.read_bytes()==raw,('literal path changed',n)

# Pinned Kani compiler feature gate; cfg(kani) only, frozen shipped body unchanged.
p=S/'crates/aspis-statement/src/lib.rs'
if not p.read_text().startswith('#![cfg_attr(kani,feature(allocator_api))]'):
 subprocess.run(['git','apply','--check',str(B/'NJL_COMPILER.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_COMPILER.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_absorption_array_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_ARRAY_WINDOW.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_ARRAY_WINDOW.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_occupancy_control_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_OCC_CONTROL.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_OCC_CONTROL.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'aspis_core::poseidon2::DIGEST_ELEMS' in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_OCC_FIX.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_OCC_FIX.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_endpoint_write_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_ENDPOINT_WINDOW.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_ENDPOINT_WINDOW.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if re.search(r'#\[kani::unwind\(4\)\][\s\S]{0,200}fn NJL_endpoint_write_cut',p.read_text()):
 subprocess.run(['git','apply','--check',str(B/'NJL_ENDPOINT_INIT.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_ENDPOINT_INIT.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_endpoint_lookup_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_LOOKUP_WINDOW.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_LOOKUP_WINDOW.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'calls:usize,kind:u8}' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_ADD_KIND.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_ADD_KIND.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_pattern_control_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATTERN_CONTROL.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATTERN_CONTROL.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'const NJL_CONSUMER_GC' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_LOOKUP_STATIC.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_LOOKUP_STATIC.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_tag_registry_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_TAG_REGISTRY.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_TAG_REGISTRY.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_tag_control_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_TAG_CONTROL.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_TAG_CONTROL.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_tag_chunk_control_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_TAG_SPLIT.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_TAG_SPLIT.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_shared_from_fn_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_SHARED_CONTROL.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_SHARED_CONTROL.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_occupancy_parent_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_OCC_PARENT.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_OCC_PARENT.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_path_parent_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATH_PARENT.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATH_PARENT.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'opened:&crate::state_only_poseidon::StateOnlyPoseidonOpenings' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATH_BORROW.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATH_BORROW.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'StateOnlyPoseidonOpeningsas usize' in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATH_TYPE_FIX.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATH_TYPE_FIX.patch')],cwd=S,check=True)
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_pattern_actual_map_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATTERN_MAP.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATTERN_MAP.patch')],cwd=S,check=True)
p=S/'crates/aspis-core/src/field.rs'
if 'pub mod NJL_observe' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATTERN_OBSERVER.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATTERN_OBSERVER.patch')],cwd=S,check=True)
suffix='\n#[cfg(kani)]\n#[path="NJL_observe.rs"]\npub mod NJL_observe;\n'.encode();field=p.read_bytes();assert field.endswith(suffix)
assert hashlib.sha256(field[:-len(suffix)]).hexdigest()=='28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea','STOP non-harness field body changed'
p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_recipient_actual_groups_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_MORE_WINDOWS.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_MORE_WINDOWS.patch')],cwd=S,check=True)
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(S/'Cargo.lock')==frozen,'STOP frozen lock mismatch before Kani'
kmx={'KMX_stubs.rs': 'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138', 'KMX_native.rs': 'cf719c47b5c8c91dcc369984c01bd0b8531b25210e344c9fd06db21b30171880', 'KMX_CopyMeaning.lean': '2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'}
for n,h in kmx.items():assert sha(S/n)==h,('KMX exact patch mismatch',n)
pins=json.loads((B/'NJL_SOURCE_PINS.json').read_text())
frozen_pins=json.loads((B/'NJL_FROZEN_FILE_PINS.json').read_text())
errors=[n for n,h in {**frozen_pins,**pins}.items() if not (S/n).is_file() or sha(S/n)!=h]
(B/(a+'-source-check.json')).write_text(json.dumps(dict(files=len(pins),errors=errors),indent=2)+'\n')
assert not errors,errors
features=x['metadata_features'] if 'metadata_features' in x else 'aspis-core/r0' if x.get('root_package')=='aspis-core' else 'aspis-r1-cost-probe-program/pool-adapter,aspis-r1-cost-probe-program/private-leaf-salts' if x.get('root_package')=='aspis-r1-cost-probe-program' else 'aspis-r1-cost-probe/optimized-terminal,aspis-r1-cost-probe/program-build'
r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1','--features',features],cwd=S,capture_output=True,text=True)
(B/(a+'-graph.stderr')).write_text(r.stderr)
assert r.returncode==0,r.stderr
(B/(a+'-graph.json')).write_text(r.stdout)
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
(B/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n');assert out['graph_matches_frozen'],out
assert sha(S/'Cargo.lock')==frozen,'STOP metadata changed lock'
status=subprocess.run(x['native_command'],cwd=B).returncode
last=sha(S/'Cargo.lock');(B/(a+'-lock-check.json')).write_text(json.dumps(dict(before=frozen,after=last,unchanged=last==frozen),indent=2)+'\n');assert last==frozen,'STOP Kani changed lock'
sys.exit(status)
