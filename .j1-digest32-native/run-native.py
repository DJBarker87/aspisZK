#!/usr/bin/env python3
import hashlib,json,os,re,signal,subprocess,sys,time
from pathlib import Path
root=Path(__file__).resolve().parent
label=sys.argv[1];tasks=json.loads((root/'tasks.json').read_text());task=tasks[label];side=task['side']
out=root/'runs'/label;out.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['run-native.py','tasks.json']:(out/name).write_bytes((root/name).read_bytes())
pins=json.loads((root/f'{side}-manifest.json').read_text());source=root/side
for p,s in pins['files'].items(): assert sha(source/p)==s,p
cg=Path('/sys/fs/cgroup')/next(s.split(':',2)[2] for s in Path('/proc/self/cgroup').read_text().splitlines() if s.startswith('0::')).lstrip('/')
read=lambda k:(cg/k).read_text().strip()
limits={k:read(k) for k in ['memory.high','memory.max','memory.swap.max']}
assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'},limits
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='stable',CARGO_TARGET_DIR=str(root/'cargo-target'),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true')
for k in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','RUSTC','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']:env.pop(k,None)
rustc=subprocess.check_output(['rustc','-Vv'],env=env,text=True);cargo=subprocess.check_output(['cargo','-V'],env=env,text=True)
assert 'commit-hash: e408947bfd200af42db322daf0fadfe7e26d3bd1' in rustc;assert cargo.startswith('cargo 1.94.1 ')
# Cargo's copied dep-info uses mtimes. Refresh after cache copy and on every
# snapshot switch; hashes remain pinned, external dependency cache is retained.
context=root/'cache-source-context.json'
manifest_sha=sha(root/f'{side}-manifest.json')
previous=json.loads(context.read_text()) if context.exists() else None
freshness={'previous_context':previous,'current_manifest_sha256':manifest_sha,'refreshed':False}
if previous is None or previous['source_manifest_sha256'] != manifest_sha:
    timestamp=time.time_ns()
    for name in pins['files']: os.utime(source/name, ns=(timestamp,timestamp))
    freshness.update(refreshed=True,refresh_timestamp_ns=timestamp,refreshed_file_count=len(pins['files']))
    context.write_text(json.dumps({'source_manifest_sha256':manifest_sha,'side':side,'timestamp_ns':timestamp},indent=2)+'\n')
(out/'source-freshness.json').write_text(json.dumps(freshness,indent=2)+'\n')
cmd=[s.replace('{root}',str(root)).replace('{side}',str(source)) for s in task['command']]
if cmd[0]=='cargo': cmd.insert(2,'--verbose')
r={'label':label,'source_revision':pins['source_revision'],'source_manifest_sha256':sha(root/f'{side}-manifest.json'),'runner_sha256':sha(Path(__file__)),'command':cmd,'cwd':str(source),'environment':{k:env[k] for k in ['PATH','RUSTUP_TOOLCHAIN','CARGO_TARGET_DIR','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE']},'cgroup':str(cg),'limits':limits,'events_before':read('memory.events'),'start_unix':time.time(),'rustc_version':rustc,'cargo_version':cargo,'expected_work':task['expected_work'],'axioms':'N/A Rust execution only','global_swap_before':subprocess.check_output(['free','-b'],text=True)}
for name in ['rustc','cargo']:
 p=Path(subprocess.check_output(['rustup','which',name],env=env,text=True).strip());r[name+'_binary']={'path':str(p),'sha256':sha(p)}
(out/'preflight.json').write_text(json.dumps(r,indent=2)+'\n')
start=time.monotonic();peak=0
with (out/'stdout.log').open('x') as log,(out/'stderr.log').open('x') as err:
 p=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],cwd=source,env=env,stdout=log,stderr=err,start_new_session=True)
 while p.poll() is None:
  peak=max(peak,int(read('memory.current')))
  if time.monotonic()-start>600:os.killpg(p.pid,signal.SIGKILL);r['timeout']=True;break
  time.sleep(.2)
 p.wait()
timing=(out/'time.log').read_text();number=lambda label: int(re.search(re.escape(label)+r':\s*(\d+)',timing)[1]) if re.search(re.escape(label)+r':\s*(\d+)',timing) else None
artifacts={}
for match in re.finditer(r"Running `([^`]+)`",(out/'stderr.log').read_text()):
    candidate=Path(match[1].split(' ')[0])
    if candidate.is_file() and str(candidate).startswith(str(root/'cargo-target')):
        artifacts[str(candidate)]={'sha256':sha(candidate),'bytes':candidate.stat().st_size}
dep_info={}
for dep in (root/'cargo-target/release').rglob('*.d'):
    if dep.stat().st_mtime >= r['start_unix'] and (dep.name.startswith(('aspis','digest_schedule','validated_prefix','r1_hash','j1_terminal'))):
        text=dep.read_text(); dest=out/'dep-info'/dep.name;dest.parent.mkdir(exist_ok=True);dest.write_text(text)
        dep_info[str(dep)]={'sha256':sha(dep),'mentions_current_source':str(source) in text}
r['artifacts']=artifacts;r['dep_info']=dep_info
r.update(exit=p.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=number('Maximum resident set size (kbytes)'),process_swaps=number('Swaps'),cgroup_peak_bytes=int(read('memory.peak')),sampled_peak_bytes=peak,events_after=read('memory.events'),swap_current_bytes=int(read('memory.swap.current')),stdout_sha256=sha(out/'stdout.log'),stderr_sha256=sha(out/'stderr.log'))
if 'expected_tests' in task:
    counts=[int(n) for n in re.findall(r'test result: ok\. (\d+) passed;', (out/'stdout.log').read_text())]
    r['expected_tests']=task['expected_tests'];r['passed_test_counts']=counts
    if counts != [task['expected_tests']]:r['validation_failure']='Unexpected test count; not accepted as a test gate'
(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['label','exit','wall_seconds','peak_rss_kib','cgroup_peak_bytes','swap_current_bytes']}),flush=True)
print((out/'stderr.log').read_text()[-2500:],flush=True)
if (out/'stdout.log').stat().st_size<10000:print((out/'stdout.log').read_text()[-3000:],flush=True)
sys.exit(p.returncode or (105 if r.get("validation_failure") else 0))
