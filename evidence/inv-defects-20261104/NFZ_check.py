"""Single debug type-check build and two independent compiler representations."""
from pathlib import Path
import subprocess,os,json,hashlib,tomllib,sys
B=Path(__file__).resolve().parent;S=B/'NFZ_src';cargo='/home/dombarker/.cargo/bin/cargo'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((B/'NFZ_SOURCE_PINS.json').read_text());expected=pins['files']['Cargo.lock']
assert all(sha(S/p)==h for p,h in pins['files'].items())
features='pool-adapter,private-leaf-salts';manifest=str(S/'programs/r1-cost-probe/Cargo.toml')
cmd=[cargo,'+nightly-2026-09-17','metadata','--manifest-path',manifest,'--locked','--offline','--format-version','1','--features',features]
r=subprocess.run(cmd,capture_output=True,text=True);(B/'NFZ_METADATA.stderr').write_text(r.stderr);assert r.returncode==0,r.stderr
m=json.loads(next(l for l in r.stdout.splitlines() if l.startswith('{')));(B/'NFZ_METADATA.json').write_text(json.dumps(m,indent=1))
lock=tomllib.loads((S/'Cargo.lock').read_text());key=lambda p:(p['name'],p['version'],p.get('source'));f={key(p):p for p in lock['package']};a={key(p):p for p in m['packages']};nodes={p['id']:p for p in m['resolve']['nodes']};pkgs={p['id']:p for p in m['packages']};errors=[]
for p in m['packages']:
 for d in nodes[p['id']]['dependencies']:
  q=pkgs[d];ok=False
  for label in f[key(p)].get('dependencies',[]):
   v=label.split(' ')
   if v[0]==q['name'] and (len(v)<2 or v[1]==q['version']) and (len(v)<3 or v[2].strip('()')==q.get('source')):ok=True
  if not ok:errors.append([key(p),key(q)])
# Part 2 repair of NFZ_B001 metadata projection, authorized for NFZ_B002.
# Cargo omits the disabled optional z4 root and its two local dependencies.
# Match NFQ's frozen graph projection, with no extra or mismatched edge allowed.
allowed_missing={('aspis-r1-cert-build','0.0.0',None),('aspis-r1-cert-check','0.0.0',None),('aspis-z4b-probe','0.1.0',None)}
assert tomllib.loads((S/'crates/aspis-r1-cost-probe/Cargo.toml').read_text())['dependencies']['aspis-z4b-probe']['optional'] is True
assert not any('r1p-check' in n['features'] for n in nodes.values())
check=dict(command=cmd,graph_matches_frozen=not(set(a)-set(f)) and not((set(f)-set(a))-allowed_missing) and not errors,added=sorted(set(a)-set(f),key=str),missing=sorted(set(f)-set(a),key=str),edge_errors=errors,lock_sha256=expected,features=[dict(name=pkgs[i]['name'],version=pkgs[i]['version'],features=n['features']) for i,n in nodes.items()])
(B/'NFZ_GRAPH_CHECK.json').write_text(json.dumps(check,indent=1));assert check['graph_matches_frozen'],check
assert sha(S/'Cargo.lock')==expected
for tool in ['rustc','cargo']:
 r=subprocess.run(['/home/dombarker/.cargo/bin/'+tool,'+nightly-2026-09-17','-Vv'],capture_output=True,text=True);(B/('NFZ_'+tool+'_VERSION.txt')).write_text(r.stdout+r.stderr);assert r.returncode==0
cmd=[cargo,'+nightly-2026-09-17','check','--manifest-path',manifest,'--locked','--offline','--features',features,'--lib','-j','4','--target-dir',str(B/'NFZ_target')]
(B/'NFZ_BUILD_COMMAND.json').write_text(json.dumps(cmd));rc=subprocess.run(cmd,cwd=S).returncode
assert all(sha(S/p)==h for p,h in pins['files'].items()), 'frozen source changed during check'
(B/'NFZ_LOCK_CHECK.json').write_text(json.dumps(dict(before=expected,after=sha(S/'Cargo.lock'),unchanged=sha(S/'Cargo.lock')==expected)))
assert sha(S/'Cargo.lock')==expected
sys.exit(rc)
