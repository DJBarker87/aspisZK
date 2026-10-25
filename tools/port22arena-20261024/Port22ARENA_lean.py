#!/usr/bin/env python3
"""Pinned warm local j1/M4400, atomic shared lock, aggregate 8GiB guard."""
import hashlib,json,os,pathlib,re,subprocess,sys,time,threading
from Port22ARENA_closure import closure, verify
R=pathlib.Path(__file__).resolve().parents[2]; E=R/'evidence/port22arena-20261024'
L=R/'docs/research/100bit-spend-path-20261013/lean'; O=pathlib.Path('/tmp/port22arena-20261024-objects'); O.mkdir(exist_ok=True)
module=sys.argv[1]; assert module.startswith('Port22ARENA_')
source=L/(module+'.lean'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=R/'docs/research/100bit-spend-path-20261013/evidence/port-integrate-20261021/OraclePortFrozenOrderActualChecks-1/command.json'
j=json.loads(base.read_text()); paths=[str(O),'/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']
deps=[]
for name in re.findall(r'^import (\S+)',source.read_text(),re.M):
 obj=next(pathlib.Path(p)/(name.replace('.','/')+'.olean') for p in paths if (pathlib.Path(p)/(name.replace('.','/')+'.olean')).is_file())
 sp=L/(name.replace('.','/')+'.lean')
 deps.append(dict(module=name,object_path=str(obj),object_sha256=sha(obj),source_sha256=sha(sp) if sp.exists() else None))
full=closure([d['module'] for d in deps], L, O)
fingerprint=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest(); source_hash=sha(source)
prior=sorted(E.glob('lean-*')); assert len(prior)<13
for p in prior:
 c=json.loads((p/'command.json').read_text())
 assert (c['source_sha256'],c['deps_fingerprint']) != (source_hash,fingerprint), 'unchanged source/deps refused'
attempt=f'lean-{len(prior)+1:03d}'; out=E/attempt;out.mkdir()
argv=[j['argv'][0],'-j1','-M4400','-DElab.async=false','-R',str(L),'-o',str(O/(module+'.olean')),str(source)]
cfg=dict(attempt=attempt,module=module,argv=argv,source_sha256=source_hash,dependencies=deps,deps_fingerprint=fingerprint,
 lean_path=':'.join(paths),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 tool_sha256=sha(pathlib.Path(argv[0])),inherited_command_sha256=sha(base),reuse='warm immutable imported objects; not a coherent release replay',
 aggregate_limit_bytes=8*1024**3,expected_time='focused elaboration against warm objects; no cold build')
cfg['dependency_closure_fingerprint']=full['fingerprint']
cfg['runner_sha256']=sha(pathlib.Path(__file__))
(out/'dependency-closure.json').write_text(json.dumps(full,indent=2)+'\n')
(out/'command.json').write_text(json.dumps(cfg,indent=2)+'\n');(out/'source.lean.txt').write_bytes(source.read_bytes())
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
def rss():
 lines=subprocess.check_output(['ps','-axo','pid=,rss=,comm='],text=True).splitlines(); vals=[]
 for line in lines:
  f=line.split(None,2)
  if len(f)==3 and pathlib.Path(f[2]).name in ['lean','lake']: vals.append(dict(pid=int(f[0]),rss_bytes=int(f[1])*1024))
 return vals
while True:
 try:lock.mkdir()
 except FileExistsError:
  print('Waiting for shared local Lean lock',flush=True);time.sleep(15);continue
 initial=rss()
 if initial:
  lock.rmdir(); print('Waiting for existing Lean processes',flush=True);time.sleep(15);continue
 break
metrics={'peak_aggregate_lean_rss_bytes':0,'guard_killed':False}; stop=threading.Event()
try:
 verify(full)
 assert sha(source)==source_hash
 for d in deps: assert sha(pathlib.Path(d['object_path']))==d['object_sha256']
 (out/'admission.json').write_text(json.dumps(dict(processes=initial,new_limit_MiB=4400,aggregate_limit_bytes=8*1024**3)))
 start=time.monotonic()
 with (out/'lean.log').open('w') as log:
  proc=subprocess.Popen(['/usr/bin/time','-l',*argv],cwd=R,env=dict(os.environ,LEAN_PATH=':'.join(paths)),stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while proc.poll() is None:
   rows=rss(); total=sum(r['rss_bytes'] for r in rows)
   metrics['peak_aggregate_lean_rss_bytes']=max(total,metrics['peak_aggregate_lean_rss_bytes'])
   if total>=8*1024**3:
    metrics['guard_killed']=True;os.killpg(proc.pid,15)
   time.sleep(.15)
  code=proc.returncode
 wall=time.monotonic()-start
finally:lock.rmdir()
log=(out/'lean.log').read_text(); maxrss=re.search(r'(\d+)\s+maximum resident set size',log); swaps=re.search(r'(\d+)\s+swaps',log)
receipt=dict(**cfg,exit_status=code,wall_seconds=wall,peak_rss_bytes=int(maxrss[1]) if maxrss else None,swaps=int(swaps[1]) if swaps else None,
 print_axioms=re.findall(r"'[^\n]+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log),**metrics,
 object_sha256=sha(O/(module+'.olean')) if code==0 else None)
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']}));print(log if code else '')
sys.exit(code)
