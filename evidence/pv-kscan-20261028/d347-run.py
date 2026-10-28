"""Serial, fail-closed capped codegen/inspection; never invokes a solver."""
from pathlib import Path
import json,subprocess,sys,os,time,hashlib,collections,re
R=Path('/home/dombarker/project-offloads/codex-pv-kscan-20261028'); B='/home/dombarker/.kani/kani-0.67.0/bin/'; SC=R.parent/'codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def admit(out,requested):
 cmd=['python3',str(SC),str(out),'--requested-bytes',str(requested)]
 p=subprocess.run(cmd,capture_output=True,text=True);j=json.loads(out.read_text())
 return p.returncode==0 and j.get('allowed') is True
name=sys.argv[1];out=R/'d347'/name;out.mkdir(parents=True,exist_ok=True)
plan=json.loads((R/'d347-plans.json').read_text())[name]
if len(sys.argv)==2:
 if not admit(out/'admission.json',8*2**30):sys.exit(78)
 cmd=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(out/'time.log'),'python3',__file__,name,'inner']
 start=time.monotonic();p=subprocess.run(cmd)
 (out/'scope.json').write_text(json.dumps(dict(command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-start,source_revision=json.loads((R/'d347-input.json').read_text())['head'],print_axioms='N/A: codegen/inspection only'),indent=2)+'\n');sys.exit(p.returncode)
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip());limits={x:(cg/x).read_text().strip() for x in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
(out/'limits.json').write_text(json.dumps(limits,indent=2)+'\n')
if not admit(out/'barrier.json',0):sys.exit(78)
if 'updates_file' in plan:
 for p,t in json.loads(Path(plan['updates_file']).read_text()).items():
  p=Path(p);assert p.is_relative_to(R/'d347');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
for p,h in plan.get('source_checks',{}).items():assert digest(p)==h,(p,'source changed')
if 'command' in plan:
 cmd=plan['command'];assert '--only-codegen' in cmd and '--keep-temps' in cmd
 env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_TARGET_DIR=str(out/'target'),RUSTFLAGS='--cfg kani')
 for k,v in plan.get('env',{}).items():
  if v is None:env.pop(k,None)
  else:env[k]=v
 with (out/'output.log').open('w') as f:p=subprocess.run(['timeout','300','taskset','--cpu-list','0-3',*cmd],cwd=plan['cwd'],env=env,stdout=f,stderr=subprocess.STDOUT)
 (out/'codegen.json').write_text(json.dumps(dict(command=cmd,exit=p.returncode,environment={k:env[k] for k in env if k.startswith(('CARGO_','RUSTFLAGS'))}),indent=2)+'\n')
 if p.returncode:sys.exit(p.returncode)
entries=plan.get('existing',[])
for directory in plan.get('metadata_dirs',[]):
 for p in Path(directory).rglob('*.kani-metadata.json'):
  for h in json.loads(p.read_text()).get('proof_harnesses',[]):
   if h['pretty_name'] not in plan['harnesses']:continue
   f=Path(h['goto_file']);f=f.with_name(f.name.replace('.symtab.out','.out'))
   if f.exists():entries.append(dict(harness=h,goto=str(f),metadata_path=str(p),metadata_sha256=digest(p)))
rows=[]; (out/'graphs').mkdir(exist_ok=True)
for e in entries:
 h=e['harness'];f=Path(e['goto']);cmd=[B+'goto-instrument','--call-graph',str(f)];p=subprocess.run(cmd,capture_output=True,text=True,timeout=60);assert p.returncode==0,p.stderr
 edges=[l.split(' -> ',1) for l in p.stdout.splitlines() if ' -> ' in l];adj=collections.defaultdict(list)
 for a,b in edges:adj[a].append(b)
 root=h['mangled_name'];q=collections.deque([root]);paths={root:[root]}
 while q:
  a=q.popleft()
  for b in adj[a]:
   if b not in paths:paths[b]=paths[a]+[b];q.append(b)
 assert root in adj or root in p.stdout,('missing root',root)
 label=h['pretty_name'].replace('::','__')+'-'+digest(f)[:12];g=out/'graphs'/(label+'.txt');g.write_text(p.stdout)
 rows.append(dict(harness=h['pretty_name'],metadata=h,origin_metadata=e['metadata_path'],metadata_sha256=e['metadata_sha256'],goto_path=str(f),goto_sha256=digest(f),goto_size=f.stat().st_size,graph_file=str(g.relative_to(out)),graph_sha256=digest(g),command=cmd,reachable_symbols=sorted(paths),copy_paths={k:paths[k] for k in ['memcpy','memmove'] if k in paths},copy_predecessors=[dict(caller=a,builtin=b) for a,bs in adj.items() if a in paths for b in bs if b in ['memcpy','memmove']]))
(out/'goto-scan.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,len(rows),[(r['harness'],list(r['copy_paths'])) for r in rows],flush=True)
