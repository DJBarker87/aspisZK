from pathlib import Path
import subprocess,json,tomllib,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-prepare1-20261027'
def check(a,package='aspis-r1-cost-probe'):
 code="""from pathlib import Path
import hashlib,json
b=Path('/home/dombarker/project-offloads/codex-cx-native-prepare1-20261027/NBA_src')
x=json.loads("""+repr((E/'NBA_SOURCE.json').read_text())+""")['source_sha256']
errors=[n for n,h in x.items() if hashlib.sha256((b/n).read_bytes()).hexdigest()!=h]
print(json.dumps(dict(files=len(x),errors=errors)))
assert not errors,errors
"""
 import shlex
 v=subprocess.run(['ssh',H,'python3'],input=code,capture_output=True,text=True)
 (E/(a+'-source-check.json')).write_text(v.stdout)
 assert v.returncode==0,v.stderr
 r=subprocess.run(['ssh',H,f'cd {B}/NBA_src && CARGO_NET_OFFLINE=true /home/dombarker/.cargo/bin/cargo metadata --locked --offline --format-version 1'],capture_output=True,text=True)
 (E/(a+'-graph.stderr')).write_text(r.stderr)
 assert r.returncode==0,r.stderr
 m=json.loads(next(l for l in r.stdout.splitlines() if l.startswith('{')));lock=tomllib.loads(Path('Cargo.lock').read_text());key=lambda p:(p['name'],p['version'],p.get('source'))
 frozen={key(p):p for p in lock['package']};actual={key(p):p for p in m['packages']};nodes={p['id']:p for p in m['resolve']['nodes']};pkgs={p['id']:p for p in m['packages']}
 added=sorted(set(actual)-set(frozen),key=str);missing=sorted(set(frozen)-set(actual),key=str);expected_unselected={('aspis-r1-cert-build','0.0.0',None),('aspis-r1-cert-check','0.0.0',None),('aspis-z4b-probe','0.1.0',None)};unexpected_missing=set(missing)-expected_unselected;errors=[]
 for p in m['packages']:
  for d in nodes[p['id']]['dependencies']:
   q=pkgs[d];ok=False
   for label in frozen[key(p)].get('dependencies',[]):
    f=label.split(' ')
    if len(f)==1 and sum(k[0]==q['name'] for k in frozen)>1:continue
    if f[0]==q['name'] and (len(f)<2 or f[1]==q['version']) and (len(f)<3 or f[2].strip('()')==q.get('source')):ok=True
   if not ok:errors.append([key(p),key(q)])
 root=next(p['id'] for p in m['packages'] if p['name']==package);seen=set()
 def visit(i):
  if i in seen:return
  seen.add(i)
  for d in nodes[i]['dependencies']:visit(d)
 visit(root)
 closure=[{'name':pkgs[i]['name'],'version':pkgs[i]['version'],'source':pkgs[i].get('source'),'features':nodes[i]['features']} for i in sorted(seen)]
 out={'selected_package':package,'selected_closure':closure,'frozen_packages':len(frozen),'resolved_packages':len(actual),'new_package_tuples':added,'missing_package_tuples':missing,'edge_errors':errors,'graph_sha256':hashlib.sha256(r.stdout.encode()).hexdigest(),'lock_sha256':hashlib.sha256(Path('Cargo.lock').read_bytes()).hexdigest(),'unselected_frozen_roots':missing,'unexpected_missing':sorted(unexpected_missing,key=str),'graph_matches_frozen':not added and not unexpected_missing and not errors}
 (E/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n')
 assert not added and not unexpected_missing and not errors,out
