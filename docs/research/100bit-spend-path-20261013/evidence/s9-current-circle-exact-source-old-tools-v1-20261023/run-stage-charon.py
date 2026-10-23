from pathlib import Path
import hashlib, json, os, re, signal, subprocess, sys, time
W = Path(__file__).resolve().parent
G = 1024**3
config = json.loads((W / 'attempt-config.json').read_text())
pins = json.loads((W / 'source-identities.json').read_text())
assert subprocess.run([sys.executable, str(W / 'check_sourcecut.py')]).returncode == 0
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
charon = Path(config['charon_path'])
assert sha(charon) == config['charon_sha256']
assert sha(Path(config['collector'])) == config['collector_sha256']
cgline = Path('/proc/self/cgroup').read_text().strip()
assert cgline.startswith('0::'), cgline
cg = Path('/sys/fs/cgroup') / cgline[3:].lstrip('/')
limits = {k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
want = {'memory.high':str(config['scope_memory_high_bytes']), 'memory.max':str(config['scope_memory_max_bytes']), 'memory.swap.max':'0'}
assert limits == want, (limits,want)
run = W / 'runs-charon'
run.mkdir(exist_ok=False)
llbc = run / 'actual-current-circle.llbc'
argv = [str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default']
for item in config['charon_includes']:
    argv += ['--include',item]
for item in config['start_from']:
    argv += ['--start-from',item]
for item in config['opaque_arithmetic_methods']:
    argv += ['--opaque',item]
argv += ['--dest-file',str(llbc),'--','--manifest-path',str(W/config['cargo_manifest']),'--locked','--offline','--release','--lib','--no-default-features','--features',','.join(config['cargo_features']),'-p',config['cargo_package'],'--jobs','1']
env = os.environ.copy()
env.update({'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':config['rustup_toolchain'],'CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_TARGET_DIR':config['target_dir']})
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS'):
    env.pop(k,None)
command = {'phase':'charon','argv':argv,'cwd':str(W/config['cargo_manifest'].rsplit('/',1)[0]),'limits':limits,'cgroup':str(cg),'start_from':config['start_from'],'opaque_arithmetic_methods':config['opaque_arithmetic_methods'],'source_identity_sha256':sha(W/'source-identities.json'),'input_cargo_lock_sha256':sha(W/'input/Cargo.lock'),'tool_pins':{str(charon):config['charon_sha256']}}
(run/'command.json').write_text(json.dumps(command,indent=2)+'\n')
(run/'environment.json').write_text(json.dumps({k:env[k] for k in ('PATH','RUSTUP_TOOLCHAIN','CARGO_NET_OFFLINE','CARGO_BUILD_JOBS','CARGO_TARGET_DIR')},indent=2)+'\n')
before = (cg/'memory.events').read_text()
start = time.monotonic(); timed = False
with (run/'stdout.log').open('x') as out:
    proc = subprocess.Popen(['/usr/bin/time','-v','-o',str(run/'time.log'),*argv],cwd=W/config['cargo_manifest'].rsplit('/',1)[0],env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
    while proc.poll() is None:
        if time.monotonic()-start > 600:
            timed=True; os.killpg(proc.pid,signal.SIGTERM)
            try: proc.wait(timeout=3)
            except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL); proc.wait()
            break
        time.sleep(.1)
status=proc.returncode
receipt={**command,'exit_status':status,'timed_out':timed,'wall_seconds':round(time.monotonic()-start,3),'swap_current_bytes':int((cg/'memory.swap.current').read_text()),'memory_peak_bytes':int((cg/'memory.peak').read_text()),'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'finished_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
t=(run/'time.log').read_text(); m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t); receipt['max_process_rss_kib']=int(m.group(1)) if m else None
if llbc.exists(): receipt['llbc_sha256']=sha(llbc); receipt['llbc_bytes']=llbc.stat().st_size
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2)); sys.exit(status if status is not None else 1)
