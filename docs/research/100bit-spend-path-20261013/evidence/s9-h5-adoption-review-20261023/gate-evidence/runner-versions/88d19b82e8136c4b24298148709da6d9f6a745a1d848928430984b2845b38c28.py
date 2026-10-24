from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time

W=Path(__file__).resolve().parent
phase,attempt=sys.argv[1:3]
cfg=json.loads((W/'commands.json').read_text())[phase]
out=W/'runs'/phase/attempt
out.mkdir(parents=True,exist_ok=False)
src=W/'work/src'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=json.loads((src/'s9-candidate-source-manifest.json').read_text())
actual={r:sha(src/r) for r in manifest['files']}
assert actual==manifest['files'],'H5 source changed'
for r,h in json.loads((W/'candidate-source-pins.json').read_text()).items():assert sha(src/r)==h
extras=json.loads((W/'extra-source-pins.json').read_text()) if (W/'extra-source-pins.json').exists() else {}
for r,d in extras.items():assert sha(src/r)==d['sha256']
G=1024**3
CG=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().removeprefix('0::').lstrip('/')
limits={k:(CG/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max']}
assert limits=={'memory.high':str(3*G),'memory.max':str(4*G),'memory.swap.max':'0'},limits
argv=cfg['argv']
assert '--release' in argv and '-j1' in argv,'optimized single-job gate required'
env=dict(os.environ)
for n in ['CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']:
 env.pop(n,None)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=cfg['target'],RUSTFLAGS='-C link-arg=-Wl,--threads=1')
os.umask(0o077)
command={'phase':phase,'attempt':attempt,'argv':argv,'cwd':str(src),'expected_time':cfg['expected_time'],'env':{k:env[k] for k in ['PATH','CARGO_NET_OFFLINE','CARGO_BUILD_JOBS','CARGO_TARGET_DIR','RUSTFLAGS']},'candidate_source_pins':json.loads((W/'candidate-source-pins.json').read_text()),'admitted_source_manifest_sha256':sha(src/'s9-candidate-source-manifest.json'),'admitted_source_files':actual,'extra_source_pins':extras,'limits':limits,'runner_sha256':sha(__file__),'source_revision':'isolated H5 snapshot on76d32f4680a19b9609522decfdb6cdbc3e5e923b; source inventory is authoritative'}
(out/'command.json').write_text(json.dumps(command,indent=2)+'\n')
before=(CG/'memory.events').read_text();start=time.monotonic();watchdog=None
with (out/'stdout.log').open('x') as log:
 p=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'time.log'),*argv],cwd=src,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  text=(out/'stdout.log').read_text()
  compiled=re.findall(r'^\s*Compiling ([\w-]+) v',text,re.M)
  allowed=lambda n:n.startswith('aspis-') or (phase=='readonly-build' and n=='litesvm')
  unexpected=sorted(set(n for n in compiled if not allowed(n)))
  if unexpected:watchdog='unexpected_dependency_compile_review:'+','.join(unexpected)
  elif time.monotonic()-start>600:watchdog='mandatory600second_review'
  if watchdog:
   os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
   break
  time.sleep(.1)
 status=p.wait()
timing=(out/'time.log').read_text() if (out/'time.log').exists() else ''
rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
verification_failure = 'zero_tests_matched' if phase.startswith('native-') and status==0 and not re.search(r'running [1-9][0-9]* tests?',(out/'stdout.log').read_text()) else None
compiled_packages=sorted(set(re.findall(r'^\s*Compiling ([\w-]+) v',(out/'stdout.log').read_text(),re.M)))
missing_compiles=[n for n in cfg.get('require_compiled',[]) if n not in compiled_packages]
if missing_compiles and status==0:verification_failure='missing_required_compile:'+','.join(missing_compiles)
receipt={'verification_failure':verification_failure,'exit_status':status,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(rss[1]) if rss else None,'scope_peak_bytes':int((CG/'memory.peak').read_text()),'scope_swap_bytes':int((CG/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(CG/'memory.events').read_text(),'watchdog_abort':watchdog,'limits':limits,'command_sha256':sha(out/'command.json'),'candidate_source_pins':command['candidate_source_pins'],'stdout_sha256':sha(out/'stdout.log'),'compiled_packages':sorted(set(re.findall(r'^\s*Compiling ([\w-]+) v',(out/'stdout.log').read_text(),re.M)))}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
raise SystemExit(status if status else (90 if watchdog else (91 if verification_failure else 0)))
