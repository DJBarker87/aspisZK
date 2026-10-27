from pathlib import Path
import subprocess,json,tomllib,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027'
def check(a):
 pre=subprocess.run(['ssh',H,f'sha256sum {B}/LPk_src/Cargo.lock'],capture_output=True,text=True)
 (E/(a+'-lock-before.log')).write_text(pre.stdout+pre.stderr)
 assert pre.returncode==0 and pre.stdout.split()[0]=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 r=subprocess.run(['ssh',H,f'cd {B}/LPk_src && CARGO_NET_OFFLINE=true /home/dombarker/.cargo/bin/cargo metadata --locked --offline --format-version 1'],capture_output=True,text=True)
 (E/(a+'-graph.stderr')).write_text(r.stderr)
 assert r.returncode==0,r.stderr
 m=json.loads(r.stdout);frozen_bytes=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock']);lock=tomllib.loads(frozen_bytes.decode());key=lambda p:(p['name'],p['version'],p.get('source'))
 frozen={key(p):p for p in lock['package']};actual={key(p):p for p in m['packages']};nodes={p['id']:p for p in m['resolve']['nodes']};pkgs={p['id']:p for p in m['packages']}
 added=sorted(set(actual)-set(frozen),key=str);errors=[]
 for p in m['packages']:
  for d in nodes[p['id']]['dependencies']:
   q=pkgs[d];ok=False
   for label in frozen[key(p)].get('dependencies',[]):
    f=label.split(' ')
    if f[0]==q['name'] and (len(f)<2 or f[1]==q['version']) and (len(f)<3 or f[2].strip('()')==q.get('source')):ok=True
   if not ok:errors.append([key(p),key(q)])
 out={'resolved_packages':len(actual),'new_package_tuples':added,'edge_errors':errors,'graph_sha256':hashlib.sha256(r.stdout.encode()).hexdigest(),'lock_sha256':hashlib.sha256(frozen_bytes).hexdigest(),'graph_matches_frozen':not added and not errors}
 (E/(a+'-graph-check.json')).write_text(json.dumps(out,indent=2)+'\n')
 assert not added and not errors,out
