"""One pinned, private Lean module; called only inside the admitted capped runner."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time,re
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');ident,module,want=sys.argv[1:]
assert re.fullmatch('750[0-9]{2}',ident)
p=H/'lean'/(module.replace('.','/')+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==want
D=H/'lean-results';D.mkdir(exist_ok=True);out=D/(ident+'.json');assert not out.exists()
for q in D.glob('*.json'):
 old=json.loads(q.read_text());assert not(old.get('source_sha256')==sha and old.get('failure_class') in ['elaboration','proof_or_elaboration_timeout']), 'unchanged failed proof/elaboration source forbidden'
subprocess.run(['python3',str(H/'authority-preflight.py')],check=True)
roots=json.loads((H/'lean-roots.json').read_text());objects=H/'lean-objects';objects.mkdir(exist_ok=True)
J=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
env=dict(os.environ,PATH=J['PATH'],LEAN_PATH=':'.join([str(objects),*roots]),LEAN_SYSROOT=J['LEAN_SYSROOT'],ELAN_TOOLCHAIN=J['ELAN_TOOLCHAIN'])
obj=objects/(module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
cmd=[J['LEAN'],'-M7000','-o',str(obj),str(p)]
start=time.monotonic()
try:
 r=subprocess.run(cmd,cwd=H/'lean',env=env,text=True,capture_output=True,timeout=900)
 timed_out=False
except subprocess.TimeoutExpired as exc:
 def decoded(s):return s.decode() if isinstance(s,bytes) else (s or '')
 r=subprocess.CompletedProcess(cmd,124,decoded(exc.stdout),decoded(exc.stderr))
 timed_out=True
print(r.stdout,end='');print(r.stderr,end='',file=sys.stderr)
record=dict(id=ident,module=module,source_sha256=sha,command=cmd,lean_path=env['LEAN_PATH'],exit=r.returncode,wall=time.monotonic()-start,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest() if r.returncode==0 else None,failure_class=None if r.returncode==0 else ('proof_or_elaboration_timeout' if timed_out else 'environment' if re.search(r'object file .*does not exist|unknown module prefix|unknown package',r.stdout+r.stderr) else 'elaboration'))
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
record['cgroup']={n:(cg/n).read_text().strip() for n in ['memory.peak','memory.high','memory.max','memory.swap.current','memory.swap.max','memory.events','pids.max','pids.events']}
out.write_text(json.dumps(record,indent=2)+'\n');print('LEAN_RESULT',json.dumps(record),flush=True);raise SystemExit(r.returncode)
