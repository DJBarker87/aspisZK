from pathlib import Path
import hashlib,json,os,subprocess,time,signal,re
w=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
rel=next(l.split(':',2)[2] for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0::'));cg=Path('/sys/fs/cgroup')/rel.lstrip('/')
read=lambda p:p.read_text().strip()
limits={k:read(cg/k) for k in ['memory.high','memory.max','memory.swap.max']};assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
out=w/'charon-build-a';out.mkdir(exist_ok=False)
rt=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
runtime={str(p):h(p) for p in [rt/'bin/rustc',rt/'bin/cargo',*list((rt/'lib/rustlib/x86_64-unknown-linux-gnu/lib').glob('librustc_driver-*.so'))]}
args=['/usr/bin/time','-v','-o',str(out/'time.log'),'/home/dombarker/.cargo/bin/cargo','+nightly-2026-06-01','build','--release','--locked','--offline','-j1','--bin','charon','--bin','charon-driver']
env=dict(os.environ);env.update(CARGO_TARGET_DIR=str(w/'charon-target'),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin')
for k in ['RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER']:env.pop(k,None)
pre={'command':args,'cwd':str(w/'charon/charon'),'runtime':runtime,'limits':limits,'cgroup':str(cg),'source_archive_pins':json.loads((w/'inputs/source-archives.json').read_text()),'dependency_pins_sha256':h(w/'charon-dependency-pins.json'),'memory_events_before':read(cg/'memory.events')}
(out/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n');begin=time.monotonic();peak=0
with (out/'build.log').open('w') as log:
 p=subprocess.Popen(args,cwd=w/'charon/charon',env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  peak=max(peak,int(read(cg/'memory.current')))
  if time.monotonic()-begin>600:os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.2)
 rc=p.wait()
r={**pre,'exit_status':rc,'wall_seconds':round(time.monotonic()-begin,3),'sampled_cgroup_peak_bytes':peak,'cgroup_memory_peak':read(cg/'memory.peak'),'cgroup_swap_current':read(cg/'memory.swap.current'),'memory_events_after':read(cg/'memory.events')}
s=(out/'time.log').read_text()
for key,field in [('peak_process_rss_kib','Maximum resident set size (kbytes)'),('process_swaps','Swaps')]:
 m=re.search(re.escape(field)+r':\s*(\d+)',s);r[key]=int(m[1]) if m else None
if rc==0:r['binaries']={name:{'path':str(w/'charon-target/release'/name),'sha256':h(w/'charon-target/release'/name)} for name in ['charon','charon-driver']}
(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['exit_status','wall_seconds','sampled_cgroup_peak_bytes','peak_process_rss_kib','process_swaps']},indent=2));print(s[-2000:])
raise SystemExit(rc)
