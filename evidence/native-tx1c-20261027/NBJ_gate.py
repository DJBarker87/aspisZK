"""Executed inside the capped S2W command: strict frozen graph before each run."""
from pathlib import Path
import hashlib,json,subprocess,sys,tomllib,os
b=Path(__file__).resolve().parent;s=b/'NBJ_src';a=sys.argv[1];harness=sys.argv[2]
lock=s/'Cargo.lock';before=hashlib.sha256(lock.read_bytes()).hexdigest()
assert before=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
with (b/(a+'-metadata.stderr')).open('w') as err:
 r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',str(s/'Cargo.toml'),'--locked','--offline','--format-version','1'],capture_output=False,stdout=subprocess.PIPE,stderr=err,text=True)
assert r.returncode==0,(r.returncode,(b/(a+'-metadata.stderr')).read_text())
m=json.loads(r.stdout);f=tomllib.loads(lock.read_text());key=lambda p:(p['name'],p['version'],p.get('source'))
frozen={key(p):p for p in f['package']};actual={key(p):p for p in m['packages']};nodes={n['id']:n for n in m['resolve']['nodes']};pkgs={p['id']:p for p in m['packages']}
new=sorted(set(actual)-set(frozen),key=str);edges=[]
for p in m['packages']:
 if key(p) not in frozen:continue
 for depid in nodes[p['id']]['dependencies']:
  d=pkgs[depid];matches=[]
  for label in frozen[key(p)].get('dependencies',[]):
   parts=label.split(' ')
   if parts[0]!=d['name']:continue
   if len(parts)>1 and parts[1]!=d['version']:continue
   if len(parts)==1 and sum(k[0]==d['name'] for k in frozen)>1:continue
   if len(parts)>2 and parts[2].strip('()')!=d.get('source'):continue
   matches.append(label)
  if not matches:edges.append([key(p),key(d)])
out=dict(lock_before=before,new_packages=new,edge_errors=edges,metadata_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),resolved_packages=len(actual),frozen_packages=len(frozen),allowed=not new and not edges)
(b/(a+'-graph.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
assert out['allowed']
cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',str(s/'crates/aspis-r1-cost-probe/Cargo.toml'),'--target-dir',str(b/'NBJ_target'),'--lib','-j','1','-Z','unstable-options','--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse']+sys.argv[3:]
print(json.dumps(dict(command=cmd)),flush=True)
r=subprocess.run(cmd,env=os.environ)
after=hashlib.sha256(lock.read_bytes()).hexdigest();out.update(lock_after=after,unchanged=before==after,kani_exit=r.returncode)
(b/(a+'-graph.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
assert after==before,'STOP frozen lock drift'
sys.exit(r.returncode)
