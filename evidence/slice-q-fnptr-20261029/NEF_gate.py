"""Own strict validation, executed inside the admitted capped scope before Kani."""
from pathlib import Path
import json,subprocess,sys,hashlib,tomllib,os
B=Path(__file__).resolve().parent;x=json.loads((B/sys.argv[1]).read_text());a=x['attempt'];S=B/'NEF_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(S/'Cargo.lock')==frozen,'STOP frozen lock mismatch before Kani'
pins=json.loads((B/'NEF_SOURCE_PINS.json').read_text())
errors=[n for n,h in pins.items() if sha(S/n)!=h]
(B/(a+'-source-check.json')).write_text(json.dumps(dict(files=len(pins),errors=errors),indent=2)+'\n')
assert not errors,errors
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
from NEF_graph import exact_graph
out.update(exact_graph(m,lock))
features={pkgs[i]['name']:nodes[i]['features'] for i in seen}
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
