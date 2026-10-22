from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
W=Path(__file__).resolve().parent; G=1024**3; inp=W/'input'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((W/'source-pins.json').read_text())
for rel in ('Cargo.toml','Cargo.lock','src/lib.rs','src/field.rs','src/field/wide_exact.rs'):
    assert sha(inp/rel)==pins['input/'+rel]['sha256'], rel
assert sha(inp/'src/field.rs')==pins['aspis_core_field']['sha256']
assert sha(inp/'src/field/wide_exact.rs')==pins['aspis_core_wide_exact']['sha256']
for rel,key in [('source-snapshots/weights-candidate.rs','candidate_weights'),('source-snapshots/weights-frozen.rs','frozen_weights')]:
    assert sha(W/rel)==pins[key]['sha256'],rel
rx=re.compile(r'pub fn field\(bytes:&\[u8\],i:usize\)->E \{ E::from_le_bytes\(&bytes\[i\*32\.\.\(i\+1\)\*32\]\)\.unwrap\(\) \}')
def fbody(path):
    m=rx.search(path.read_text()); assert m,str(path); return m.group(0).encode()
cb=fbody(W/'source-snapshots/weights-candidate.rs'); fb=fbody(W/'source-snapshots/weights-frozen.rs'); ib=fbody(inp/'src/lib.rs')
assert cb==fb==ib and len(cb)==90 and hashlib.sha256(cb).hexdigest()==pins['field_body']['sha256']
llbc=W/'runs/charon/field-decoder.llbc'; llbc.parent.mkdir(parents=True,exist_ok=False)
tools=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016'); charon=tools/'charon-target/release/charon'
toolpins={str(charon):'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'}
for p,h in toolpins.items(): assert sha(Path(p))==h,p
cgline=Path('/proc/self/cgroup').read_text().strip(); assert cgline.startswith('0::'),cgline
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/'); limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
assert limits=={'memory.high':str(2*G),'memory.max':str(4*G),'memory.swap.max':'0'},limits
argv=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default',
      '--include','core::option::Option','--start-from','crate::weights::field','--dest-file',str(llbc),
      '--','--locked','--offline','--release','--lib','--no-default-features','--jobs','1']
env=os.environ.copy(); env.update({'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_TARGET_DIR':'/home/dombarker/project-offloads/s3-s9-scalar-fold-fullsysroot-v3-20261021/target'})
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS'): env.pop(k,None)
command={'phase':'charon','argv':argv,'cwd':str(inp),'limits':limits,'cgroup':str(cg),'tool_pins':toolpins,'candidate_weights_sha256':pins['candidate_weights']['sha256'],'frozen_weights_sha256':pins['frozen_weights']['sha256'],'candidate_field_body_sha256':pins['field_body']['sha256'],'copied_aspis_core_field_sha256':sha(inp/'src/field.rs'),'copied_wide_exact_sha256':sha(inp/'src/field/wide_exact.rs'),'expected_work':'focused Charon body extraction from exact field shim and copied actual core field/decoder source; no full workspace target'}
run=W/'runs/charon'; (run/'command.json').write_text(json.dumps(command,indent=2)+'\n'); (run/'environment.json').write_text(json.dumps({k:env[k] for k in ('PATH','RUSTUP_TOOLCHAIN','CARGO_NET_OFFLINE','CARGO_BUILD_JOBS','CARGO_TARGET_DIR')},indent=2)+'\n')
before=(cg/'memory.events').read_text(); start=time.monotonic(); timed=False
with (run/'stdout.log').open('x') as out:
    proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(run/'time.log'),*argv],cwd=inp,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
    while proc.poll() is None:
        if time.monotonic()-start>300:
            timed=True; os.killpg(proc.pid,signal.SIGTERM)
            try: proc.wait(timeout=3)
            except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL); proc.wait()
            break
        time.sleep(.1)
status=proc.returncode; wall=time.monotonic()-start
receipt={**command,'exit_status':status,'timed_out':timed,'wall_seconds':round(wall,3),'swap_current_bytes':int((cg/'memory.swap.current').read_text()),'memory_peak_bytes':int((cg/'memory.peak').read_text()),'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'finished_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
tr=(run/'time.log').read_text(); m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',tr); receipt['max_process_rss_kib']=int(m.group(1)) if m else None
if llbc.exists(): receipt['llbc_sha256']=sha(llbc); receipt['llbc_bytes']=llbc.stat().st_size
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n'); print(json.dumps(receipt,indent=2)); sys.exit(status if status is not None else 1)
