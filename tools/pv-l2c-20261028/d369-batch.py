"""Finite focused queue in one reserved scope, using unchanged run2.py per target.
Pattern: the accepted L2B batch_cursor.py. One module, ID, time and axioms
receipt per compiler invocation. Stops immediately on the first nonzero exit.
"""
from pathlib import Path
import json,subprocess,hashlib,shlex,sys,re,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028/resume-d369';H='/home/dombarker/project-offloads/codex-pv-l2c-20261028';host='dombarker@100.108.41.90'
audit='--audit' in sys.argv
native_after='--native-after' in sys.argv
args=[x for x in sys.argv[1:] if x not in ['--audit','--native-after']]
start=int(args[0]);names=args[1:]
assert (50397<=start<=50399 if audit else 50300<=start<50397) and names
if audit:assert all(m in ['PV_L2C_CombinedAudit','PV_L2C_FixtureAudit','PV_L2C_FocusedReplay','PV_L2C_D371CombinedAudit','PV_L2C_D371FixtureAudit','PV_L2C_D371FocusedReplay'] for m in names)
old=[json.loads(p.read_text()) for p in E.glob('refusal-*.json')]
if old:
 remaining=180-(datetime.datetime.now(datetime.timezone.utc)-max(datetime.datetime.fromisoformat(x['utc']) for x in old)).total_seconds()
 if remaining>0:print('WAIT',remaining,'seconds; no ID consumed');sys.exit(77)
resolution=json.loads((E/'focused-resolution.json').read_text())['resolved'];sources=json.loads((E/'focused-project-sources.json').read_text());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();spec=[]
for idx,m in enumerate(names):
 a=start+idx;assert a<=50399 if audit else a<50397
 assert not (E/f'receipt-{a}.json').exists(),a
 if m in sources:
  body=sources[m];origin=resolution[m]
  if origin['authority']=='h5 own git-tracked HEAD':
   current=subprocess.check_output(['git','show',rev+':'+origin['path']],text=True)
   assert body==current, 'Stale source resolution: '+m+'; rerun resume-resolve.py'
 else:
  p='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean';body=(R/p).read_text();origin=dict(path=p,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip(),authority='h5 own git-tracked HEAD')
 spec.append(dict(attempt=a,module=m,source=body,source_sha256=hashlib.sha256(body.encode()).hexdigest(),origin=origin,source_revision=rev))
assert len([p for p in E.glob('receipt-*.json') if json.loads(p.read_text()).get('exit') is not None])+len(spec)<=100
D=E/f'batch-{start}';D.mkdir(exist_ok=True)
def ssh(c):return subprocess.run(['ssh',host,c],capture_output=True,text=True)
# Audit every proposed ID against other jobs' receipt directories and sent.txt.
code='''import pathlib,json,re,sys
ids=json.load(sys.stdin);root=pathlib.Path('/home/dombarker/project-offloads');hits={str(a):[] for a in ids}
for job in root.glob('codex-pv-*'):
 if job.name=='codex-pv-l2c-20261028':continue
 for p in job.glob('evidence/**/*'):
  if p.is_file():
   for a in ids:
    if re.search(r'(^|[-_])'+str(a)+r'([-_.]|$)',p.name):hits[str(a)].append(str(p))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
for line in sent.read_text().splitlines():
 for a in ids:
  if re.search(r'\\b'+str(a)+r'\\b',line):hits[str(a)].append(line)
print(json.dumps(hits))
'''
p=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=json.dumps([x['attempt'] for x in spec]),capture_output=True,text=True);assert p.returncode==0,p.stderr
(D/'id-audit.json').write_text(p.stdout);assert not any(json.loads(p.stdout).values()),p.stdout
# m prime: admission alone does not consume an attempt ID.
res=f'{H}/evidence/batch-{start}-reservation'
p=ssh(f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {res}.json > {res}.log 2>&1\ns=$?\ncat {res}.log\nexit $s');(D/'preflight.log').write_text(p.stdout+p.stderr);gate=json.loads(p.stdout.strip().splitlines()[-1]);(D/'reservation.json').write_text(json.dumps(gate,indent=2)+'\n')
if p.returncode!=0 or not gate['allowed']:
 gate['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();
 (D/('refusal-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S%f')+'.json')).write_text(json.dumps(gate,indent=2)+'\n');
 (E/f'refusal-{start}.json').write_text(json.dumps(gate,indent=2)+'\n');print('REFUSED',gate);sys.exit(78)
if native_after:
 assert not audit
 assert subprocess.run(['python3',str(R/'tools/pv-l2c-20261028/generate-balance-cut.py'),'--check']).returncode==0
 assert ssh(f'mkdir -p {H}/differential').returncode==0
 subprocess.run(['scp','-q',str(R/'tools/pv-l2c-20261028/native-receipt.py'),f'{host}:{H}/native-receipt.py'],check=True)
 for fn in ['Cargo.toml','main.rs','balance_cut.rs']:
  subprocess.run(['scp','-q',str(R/'tools/pv-l2c-20261028/differential'/fn),f'{host}:{H}/differential/{fn}'],check=True)
 p0=subprocess.run(['python3',str(R/'tools/pv-l2c-20261028/native-preflight.py')],capture_output=True,text=True)
 (D/'native-preflight.log').write_text(p0.stdout+p0.stderr);assert p0.returncode==0,p0.stdout+p0.stderr
 assert ssh(f'cp /home/dombarker/project-offloads/codex-pv-integ4-20261027/source/Cargo.lock {H}/differential/Cargo.lock').returncode==0
 native_cmd=['env','PV8_SOURCE_DIR='+H+'/differential','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+H+'/differential-target','CARGO_BUILD_JOBS=4','CARGO_NET_OFFLINE=true','PV_L2C_PIN_FILES=Cargo.toml:Cargo.lock:main.rs:balance_cut.rs','PV_L2C_EXPECTED_TIME=Optimized compilation then 128 same-input native balancing differential cases','PV_L2C_EVIDENCE_CLASS=N/A: finite native validation, not universal proof','python3',H+'/native-receipt.py',H+'/evidence/native-after-'+str(start),'timeout','180','taskset','--cpu-list','0-3','cargo','run','--release','--offline','-j','4']
 (D/'native-invocation.json').write_text(json.dumps(dict(command=native_cmd,source_revision=rev,source_sha256={fn:hashlib.sha256((R/'tools/pv-l2c-20261028/differential'/fn).read_bytes()).hexdigest() for fn in ['Cargo.toml','main.rs','balance_cut.rs']},evidence_class='finite native differential',cgroup_peak_note='scope cumulative; aggregate RSS and wall time are native-stage measurements'),indent=2)+'\n')
(D/'manifest.json').write_text(json.dumps(spec)+'\n');subprocess.run(['scp','-q',str(D/'manifest.json'),f'{host}:{H}/batch-{start}.json'],check=True)
remote=r'''import json,pathlib,subprocess,hashlib,re,sys,time
H=pathlib.Path(sys.argv[1]);start=sys.argv[2];P=H/'lean';env=P/'J.json';roots=[pathlib.Path(x) for x in json.load(open(env))['LEAN_PATH'].split(':')]
for x in json.load(open(H/('batch-'+start+'.json'))):
 a=x['attempt'];m=x['module'].replace('.','/');s=P/'sources'/(m+'.lean');o=P/'objects'/(m+'.olean');s.parent.mkdir(parents=True,exist_ok=True);o.parent.mkdir(parents=True,exist_ok=True)
 if o.is_symlink():raise RuntimeError('Refuse to overwrite reused cache object '+str(o))
 s.write_text(x['source']);assert hashlib.sha256(s.read_bytes()).hexdigest()==x['source_sha256']
 deps={}
 for name in [n for line in re.findall(r'^\s*(?:(?:public|private)\s+)?import[ \t]+([^\n]+)',x['source'],re.M) for n in line.split()]:
  p=next((r/(name.replace('.','/')+'.olean') for r in roots if (r/(name.replace('.','/')+'.olean')).exists() or (r/(name.replace('.','/')+'.olean')).is_symlink()),None)
  if p is None or not p.is_file():raise RuntimeError('Missing actual import '+name)
  deps[name]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 (H/'evidence'/('deps-'+str(a)+'.json')).write_text(json.dumps(deps,sort_keys=True))
 t=time.monotonic()
 with (H/'evidence'/('out-'+str(a)+'.log')).open('w') as f:
  p=subprocess.run(['/usr/bin/time','-v','-o',str(H/'evidence'/('time-'+str(a)+'.log')),'timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(env),str(P/'objects'),str(P/'sources'),str(o),str(s),'7000'],stdout=f,stderr=subprocess.STDOUT)
  f.write('\nexit='+str(p.returncode)+'\n')
 (H/'evidence'/('done-'+str(a)+'.json')).write_text(json.dumps(dict(exit=p.returncode,wall_seconds=time.monotonic()-t)))
 print(a,m,p.returncode,flush=True)
 if p.returncode:break
'''
if native_after:
 remote+='\nnative_exit=subprocess.run('+repr(native_cmd)+').returncode\nprint(\"NATIVE EXIT\",native_exit,flush=True)\n'
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=l2c-batch-{start}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','-u','-c',remote,H,str(start)]
(D/'command.json').write_text(json.dumps(cmd,indent=2)+'\n');print('LAUNCH BATCH',start,len(spec),'serial modules',flush=True)
(D/'submitted.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),command=cmd))+'\n')
p=ssh(shlex.join(cmd));(D/'scope.log').write_text(p.stdout+p.stderr);print(p.stdout+p.stderr,flush=True)
if p.returncode==78:
 (E/f'refusal-{start}.json').write_text(json.dumps(dict(allowed=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reason='scope launcher exit78 after admission'),indent=2)+'\n');sys.exit(78)
# Recover exactly the invocations actually launched; never re-submit after SSH loss.
for x in spec:
 a=x['attempt'];q=ssh(f'cat {H}/evidence/done-{a}.json')
 if q.returncode:break
 x.update(json.loads(q.stdout));x['reservation']=gate;x['scope_command']=cmd
 for label in ['out','time','deps']:
  suffix='json' if label=='deps' else 'log';q=ssh(f'cat {H}/evidence/{label}-{a}.{suffix}');assert q.returncode==0,q.stderr;(E/f'{label}-{a}.{suffix}').write_text(q.stdout)
 out=(E/f'out-{a}.log').read_text();tim=(E/f'time-{a}.log').read_text();x['dependencies']=json.loads((E/f'deps-{a}.json').read_text());x['deps_fingerprint']=hashlib.sha256((E/f'deps-{a}.json').read_bytes()).hexdigest();x['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
 for key,pat in [('peak_rss_bytes',r'Maximum resident set size \(kbytes\): (\d+)'),('swaps',r'Swaps: (\d+)'),('host_wall',r'Elapsed \(wall clock\) time.*: (.+)')]:
  v=re.search(pat,tim);x[key]=(int(v[1])*1024 if key=='peak_rss_bytes' else v[1]) if v else None
 x['accepted']=x['exit']==0 and 'sorryAx' not in out and 'error:' not in out
 (E/f'used-{a}.json').write_text(json.dumps(dict(attempt=a,target=x['module'],utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
 (E/f'{a}-{x["module"].replace(".","_")}.lean.txt').write_text(x.pop('source'))
 (E/f'receipt-{a}.json').write_text(json.dumps(x,indent=2)+'\n');print('RECEIPT',a,x['exit'],x['host_wall'],x['peak_rss_bytes'],flush=True)
 if not x['accepted']:print(out[-5000:]);sys.exit(1)
