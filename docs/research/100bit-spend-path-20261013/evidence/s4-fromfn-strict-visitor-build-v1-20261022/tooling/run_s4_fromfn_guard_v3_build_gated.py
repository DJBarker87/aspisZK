from pathlib import Path
import contextlib, fcntl, hashlib, io, json, os, re, runpy, subprocess, time

BASE=Path('/home/dombarker/project-offloads/d18-aeneas-reborrow-v1-20261022')
WORK=BASE/'aeneas-trait-guard-v3'
EVIDENCE=BASE/'run-trait-guard-v3-strict-build-v4'
COLLECTOR=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
LOCK=Path('/tmp/aspis-global-extraction-admission-20261019.lock')
IMAGE='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
HIGH,MAX,G=1024**3,2*1024**3,1024**3
EXPECTED_COLLECTOR='4fc152ea4f88742fb460c301ae17446f1d1ba9162acdaafb37d80e60c4907800'
EXPECTED_SOURCE='0d2ab7873780feaea346facc38f5429144153f6e93a08aef636509505216bb18'
EXPECTED_BINARY='f0eff7e5b2d638aa0611de64a2dc699e805ad0168f1ef42d5500c23a18a1aecc'
EXPECTED_ASSOC='1f1b6527bce296728cce288648e6b5f6aa4fd0f1387a06af33fee2642244b616'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args, **kw): return subprocess.run(args,check=True,text=True,capture_output=True,**kw)
def time_summary(p):
 s=p.read_text() if p.exists() else ''
 def n(k):
  m=re.search(re.escape(k)+r':\s*(\d+)',s); return int(m.group(1)) if m else None
 return {'max_rss_kib':n('Maximum resident set size (kbytes)'), 'swaps':n('Swaps'), 'text':s}

assert hashlib.sha256(COLLECTOR.read_bytes()).hexdigest()==EXPECTED_COLLECTOR
assert not EVIDENCE.exists()
assert sha(WORK/'interp/InterpMatchCtxs.ml')==EXPECTED_SOURCE
assert sha(WORK/'interp/InterpStatements.ml')==EXPECTED_ASSOC
assert sha(WORK/'_build/default/main.exe')==EXPECTED_BINARY
EVIDENCE.mkdir(parents=True)
name=f'aspis-s4-v3-gated-{os.getpid()}-{time.time_ns()}'
container='aspis-s4-v3-gated-'+str(os.getpid())+'-'+str(time.time_ns())
gate='/output/START_BUILD'
shell=("set -e; echo $$ > /output/inside.pid; cat /proc/self/cgroup > /output/container-self-cgroup.before; "
       "while [ ! -f /output/START_BUILD ]; do sleep 0.1; done; "
       "cat /proc/self/cgroup > /output/container-self-cgroup.at-start; "
       "cat /sys/fs/cgroup/memory.high > /output/container.memory.high; "
       "cat /sys/fs/cgroup/memory.max > /output/container.memory.max; "
       "cat /sys/fs/cgroup/memory.swap.max > /output/container.memory.swap.max; "
       "test \"$(cat /sys/fs/cgroup/memory.high)\" = '1073741824'; "
       "test \"$(cat /sys/fs/cgroup/memory.max)\" = '2147483648'; "
       "test \"$(cat /sys/fs/cgroup/memory.swap.max)\" = '0'; "
       "/usr/bin/time -v -o /output/build.time dune build --profile release -j 1 main.exe > /output/build.log 2>&1")
basecmd=['docker','run','-d','--name',container,'--memory='+str(MAX),'--memory-swap='+str(MAX),'--cpus=2','--pids-limit=128','--user','1000:1000',
 '--mount',f'type=bind,src={WORK},dst=/work','--mount',f'type=bind,src={EVIDENCE},dst=/output','--workdir','/work','--entrypoint','opam',IMAGE,'exec','--','sh','-c',shell]
with LOCK.open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 buf=io.StringIO()
 with contextlib.redirect_stdout(buf): runpy.run_path(str(COLLECTOR))
 inv=json.loads(buf.getvalue())
 checks={'finite_plus_candidate_cap_le_48GiB':inv['effective_sum_bytes']+MAX<=48*G,
         'MemAvailable_at_least_14GiB':inv['MemAvailable_kB']*1024>=14*G}
 adm={'inventory':inv,'checks':checks,'limits_expected':{'memory.high':str(HIGH),'memory.max':str(MAX),'memory.swap.max':'0'},
      'source_sha256':EXPECTED_SOURCE,'binary_sha256_before':EXPECTED_BINARY,'command':basecmd}
 (EVIDENCE/'admission.json').write_text(json.dumps(adm,indent=2)+'\n')
 print(json.dumps({'timestamp':inv['timestamp_utc'],'finite_reserved_gib':inv['effective_sum_bytes']/G,
      'memavailable_gib':inv['MemAvailable_kB']*1024/G,'checks':checks}),flush=True)
 if not all(checks.values()): raise SystemExit('fresh admission denied; no container launched')
 start=time.monotonic()
 cid=None; pid=None; cgroup=None
 try:
  cid=run(basecmd).stdout.strip()
  (EVIDENCE/'container.id').write_text(cid+'\n')
  deadline=time.monotonic()+15
  while time.monotonic()<deadline:
   pidtxt=run(['docker','inspect','--format','{{.State.Pid}}',cid]).stdout.strip()
   if pidtxt and pidtxt!='0':
    pid=int(pidtxt)
    pg=Path(f'/proc/{pid}/cgroup')
    if pg.exists():
     line=next((x for x in pg.read_text().splitlines() if x.startswith('0::')),None)
     if line: cgroup=line[3:]; break
   time.sleep(.05)
  assert pid and cgroup, 'container process/cgroup unavailable before gate'
  assert cgroup==f'/system.slice/docker-{cid}.scope', f'unexpected cgroup path {cgroup}'
  unit=f'docker-{cid}.scope'
  run(['sudo','-n','systemctl','set-property','--runtime',unit,f'MemoryHigh={HIGH}',f'MemoryMax={MAX}','MemorySwapMax=0'])
  cg=Path('/sys/fs/cgroup')/cgroup.lstrip('/')
  limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
  assert limits=={'memory.high':str(HIGH),'memory.max':str(MAX),'memory.swap.max':'0'}, f'container cgroup limits differ: {limits}'
  owner={'container_id':cid,'host_pid':pid,'proc_cgroup':Path(f'/proc/{pid}/cgroup').read_text(),
         'systemd_unit':unit,'systemd_control_group':run(['systemctl','show',unit,'--property=ControlGroup','--value']).stdout.strip(),
         'cgroup_files':limits,'cgroup_events_before':(cg/'memory.events').read_text(),
         'scope_memory_peak_before':(cg/'memory.peak').read_text() if (cg/'memory.peak').exists() else None,
         'gate_path':gate,'gate_released_after_limit_assertions':True}
  assert owner['systemd_control_group']==cgroup
  (EVIDENCE/'owner-cgroup.json').write_text(json.dumps(owner,indent=2)+'\n')
  # The container process itself verifies its own mounted cgroup files after this gate.
  (EVIDENCE/'START_BUILD').write_text('verified\n')
  adm['registration']=owner; (EVIDENCE/'admission.json').write_text(json.dumps(adm,indent=2)+'\n')
  fcntl.flock(lock,fcntl.LOCK_UN)
  status=int(run(['docker','wait',cid],timeout=300).stdout.strip())
  log=run(['docker','logs',cid],check=True).stdout
  (EVIDENCE/'container.logs').write_text(log)
  cg2=Path('/sys/fs/cgroup')/cgroup.lstrip('/')
  post={'host_pid_cgroup_after':Path(f'/proc/{pid}/cgroup').read_text() if Path(f'/proc/{pid}').exists() else None,
        'limits_after':{k:(cg2/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')} if cg2.exists() else None,
        'memory_events_after':(cg2/'memory.events').read_text() if cg2.exists() else None,
        'memory_peak_after':(cg2/'memory.peak').read_text() if cg2.exists() and (cg2/'memory.peak').exists() else None}
  (EVIDENCE/'post-cgroup.json').write_text(json.dumps(post,indent=2)+'\n')
  receipt={'exit_status':status,'wall_seconds':time.monotonic()-start,'strict_match_source_sha256':sha(WORK/'interp/InterpMatchCtxs.ml'),
    'assoc_source_sha256':sha(WORK/'interp/InterpStatements.ml'),'binary_sha256_before':EXPECTED_BINARY,
    'binary_sha256_after':sha(WORK/'_build/default/main.exe'),'build_time':time_summary(EVIDENCE/'build.time'),
    'limits':limits,'command':basecmd,'outputs':{}}
  for f in EVIDENCE.rglob('*'):
   if f.is_file() and f.name not in ('receipt.json','admission.json'):
    receipt['outputs'][str(f.relative_to(EVIDENCE))]=sha(f)
  (EVIDENCE/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
  print(json.dumps({k:v for k,v in receipt.items() if k!='outputs'},indent=2),flush=True)
 finally:
  fcntl.flock(lock,fcntl.LOCK_UN)
  if cid:
   subprocess.run(['docker','rm','-f',cid],capture_output=True)
raise SystemExit(status)
