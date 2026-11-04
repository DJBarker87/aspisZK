"""Own strict validation, executed inside the admitted capped scope before Kani."""
from NFP_build import build
from pathlib import Path
import json,subprocess,sys,hashlib,tomllib,os
assert os.environ.get('CARGO_NET_OFFLINE')=='true','offline gate'
B=Path(__file__).resolve().parent;x=json.loads((B/sys.argv[1]).read_text());a=x['attempt'];S=B/'NFP_src'
built=build()
if sys.argv[2].startswith('full_'):
 from NFP_full_build import apply
 built.update(apply(json.loads((B/'NFP_FROZEN.json').read_text()),S))
 built['changed']['crates/aspis-r1-cost-probe/src/candidate.rs']=hashlib.sha256((S/'crates/aspis-r1-cost-probe/src/candidate.rs').read_bytes()).hexdigest()
if sys.argv[2].startswith('suffix_'):
 from NFP_split_build import apply
 built.update(apply(json.loads((B/'NFP_FROZEN.json').read_text()),S))
if sys.argv[2].startswith('frame_'):
 frozen=json.loads((B/'NFP_FROZEN.json').read_text())
 code=(B/'NFP_frame.rs.txt').read_text()
 assert 'accumulate_batched_with_node(p, &mut a, node, folded, &mut pending);\n    mark(obs, Phase::Query(i));\n    Ok((a, pending))' in frozen['crates/aspis-r1-cost-probe/src/candidate.rs']
 import re
 m=re.search(r'fn NFP_finish\([^\n]+\{(.*?)\n\}',code,re.S);assert m,'missing physical frame function'
 body=m.group(1).replace('let i=a.next;','').replace('accumulate(p,&mut a,node,folded,&mut pending,f);','accumulate_batched_with_node(p, &mut a, node, folded, &mut pending);')
 token=lambda t:re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|::|->|[^\s]',t)
 expected='accumulate_batched_with_node(p, &mut a, node, folded, &mut pending); mark(obs, Phase::Query(i)); Ok((a, pending))'
 assert token(body)==token(expected),'native physical frame erasure drift'

 (S/'crates/aspis-r1-cost-probe/src/NFP_query.rs').write_text(code)
 built.update(frame_cut='original accumulator-call/phase-mark/Ok-return',qualification='Full raw64 arbitrary mutations; arbitrary observed coordinate, real Vec moves and final frame')
if sys.argv[2].startswith('node_'):
 code=(B/'NFP_node.rs.txt').read_text()
 assert 'let node = z.mul(z).double().sub(M31::ONE);' in json.loads((B/'NFP_FROZEN.json').read_text())['crates/aspis-r1-cost-probe/src/candidate.rs']
 assert 'let node=product(z,z,p).double().sub(M31::ONE);node' in code
 (S/'crates/aspis-r1-cost-probe/src/NFP_query.rs').write_text(code)
 built.update(node_cut='same raw-z pair; scalar M31 double/sub and returned node',qualification='Only M31 native add/sub; multiplication is opaque and Lean-discharged')
if sys.argv[2].startswith('geometry_'):
 code=(B/'NFP_geometry.rs.txt').read_text();frozen=json.loads((B/'NFP_FROZEN.json').read_text())
 assert 'let inverse = *geometry.for_query(i);' in frozen['crates/aspis-r1-cost-probe/src/candidate.rs']
 assert 'let z = geometry.line_z[i - geometry.start];' in frozen['crates/aspis-r1-cost-probe/src/candidate.rs']
 assert 'fn for_query(&self,index:usize)->&[M31;5] {&self.inverses[index-self.start]}' in frozen['crates/aspis-r1-cost-probe/src/verifier.rs']
 assert 'let inverse=*geometry.for_query(i);let z=geometry.line_z[i-geometry.start];(inverse,z)' in code
 (S/'crates/aspis-r1-cost-probe/src/NFP_query.rs').write_text(code)
 built.update(geometry_cut='actual for_query and line_z with arbitrary TX1/TX2 reached index',qualification='all raw input cells, actual start/end/length, no constructor success assumed')
(B/(a+'-fission-check.json')).write_text(json.dumps(built,indent=2))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Pin the compiler/backend binaries used by the existing fixed Kani install.
version=subprocess.run([x['native_command'][0],'--version'],capture_output=True,text=True)
assert version.returncode==0 and '0.67.0' in version.stdout,(version.returncode,version.stdout,version.stderr)
tool_paths=[Path(x['native_command'][0])]+[Path('/home/dombarker/.kani/kani-0.67.0/bin')/n for n in ['kani-driver','kani-compiler','cbmc','goto-instrument']]
tools={str(p):dict(resolved=str(p.resolve()),sha256=sha(p),mtime_ns=p.stat().st_mtime_ns,ctime_ns=p.stat().st_ctime_ns) for p in tool_paths}
(B/(a+'-tool-check.json')).write_text(json.dumps(dict(version=version.stdout.strip(),binaries=tools),indent=2))
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(S/'Cargo.lock')==frozen,'STOP frozen lock mismatch before Kani'
kmx={'KMX_stubs.rs': 'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138', 'KMX_native.rs': 'cf719c47b5c8c91dcc369984c01bd0b8531b25210e344c9fd06db21b30171880', 'KMX_CopyMeaning.lean': '2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'}
for n,h in kmx.items():assert sha(S/n)==h,('KMX exact patch mismatch',n)
frozen_sources=json.loads((B/'NFP_FROZEN.json').read_text())
errors=[]
for name,text in frozen_sources.items():
 p=S/name
 if not p.is_file():continue
 if p.read_text()!=text and name not in built['changed']:errors.append(name)
(B/(a+'-source-check.json')).write_text(json.dumps(dict(errors=errors,allowed_changes=built['changed']),indent=2))
assert not errors,errors
# Rule 16: reject every static declaration in own harnesses and exact KMX files.
# This is stricter than checking writes/interior mutability only.
import re
harnesses=[p for p in S.rglob('NFP*.rs')]+[S/'KMX_stubs.rs',S/'KMX_native.rs']
static_errors=[str(p) for p in harnesses if re.search(r'\bstatic\s+(?:mut\s+)?[A-Za-z_]',p.read_text())]
(B/(a+'-rule16-check.json')).write_text(json.dumps(dict(static_declarations=static_errors,files={str(p):sha(p) for p in harnesses}),indent=2)+'\n')
assert not static_errors,('STOP rule16',static_errors)
ni=x['native_command'];manifest=ni[ni.index('--manifest-path')+1];selected=ni[ni.index('--features')+1]
r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1','--manifest-path',manifest,'--features',selected],cwd=S,capture_output=True,text=True)
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
root_name=tomllib.loads(Path(manifest).read_text())['package']['name']
visit(next(p['id'] for p in m['packages'] if p['name']==root_name))
out=dict(graph_matches_frozen=not added and not(missing-allowed_missing) and not edge_errors,frozen_packages=len(f),resolved_packages=len(actual),new_package_tuples=sorted(added,key=str),missing_package_tuples=sorted(missing,key=str),edge_errors=edge_errors,lock_sha256=frozen,graph_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),selected_closure=[dict(name=pkgs[i]['name'],version=pkgs[i]['version'],source=pkgs[i].get('source'),features=nodes[i]['features']) for i in sorted(seen)])
(B/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n');assert out['graph_matches_frozen'],out
from NFP_graph import exact_graph
out.update(exact_graph(m,lock))
features={pkgs[i]['name']:nodes[i]['features'] for i in seen}
assert features['aspis-core']==['r0'],'wrong deployed core projection'
# Verifier-root receipt: deployed verifier feature selection.
assert 'no-entrypoint' not in features.get('aspis-r1-cost-probe-program',[])
if manifest.endswith('aspis-r1-cost-probe/Cargo.toml'):assert {'default','private-leaf-salts','optimized-terminal','program-build'} <= set(features['aspis-r1-cost-probe'])
if 'aspis-statement' in features and not manifest.endswith('aspis-core/Cargo.toml'):assert {'r0','pool-v1-kernel'} <= set(features['aspis-statement'])
(B/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n')
assert sha(S/'Cargo.lock')==frozen,'STOP metadata changed lock'
out['resolved_features_all_crates']=[dict(name=p['name'],version=p['version'],source=p.get('source'),features=nodes[p['id']]['features']) for p in sorted(m['packages'],key=lambda p:p['id'])]
(B/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n')
status=subprocess.run(x['native_command'],cwd=B).returncode
last=sha(S/'Cargo.lock');(B/(a+'-lock-check.json')).write_text(json.dumps(dict(before=frozen,after=last,unchanged=last==frozen),indent=2)+'\n');assert last==frozen,'STOP Kani changed lock'
sys.exit(status)
