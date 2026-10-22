from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
W=Path(__file__).resolve().parent; G=1024**3
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest(); pins=json.loads((W/'source-pins.json').read_text())
llbc=W/'runs/charon/field-decoder.llbc'; want='e8e00fd32decf4f57595594a5bd99f6c86167743289b9569c0e2487ef2ad23f6'; assert sha(llbc)==want
obj=json.loads(llbc.read_text()); assert not obj.get('has_errors')
tools=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016'); aeneas=tools/'bin/aeneas'; charon=tools/'charon-target/release/charon'
toolpins={str(aeneas):'959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3',str(charon):'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'}
for p,h in toolpins.items(): assert sha(Path(p))==h,p
cgline=Path('/proc/self/cgroup').read_text().strip(); assert cgline.startswith('0::'),cgline
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/'); limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}; assert limits=={'memory.high':str(2*G),'memory.max':str(4*G),'memory.swap.max':'0'},limits
run=W/'runs/aeneas'; run.mkdir(parents=True,exist_ok=False); gen=run/'generated'
argv=[str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1S9CandidateFieldDecodeV1','-dest',str(gen),'-subdir','AspisR1S9CandidateFieldDecodeV1','-split-files','-emit-json',str(llbc)]
env=os.environ.copy(); env.update({'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'})
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS'):env.pop(k,None)
command={'phase':'aeneas','argv':argv,'cwd':str(W),'limits':limits,'cgroup':str(cg),'tool_pins':toolpins,'candidate_field_body_sha256':pins['field_body']['sha256'],'reused_llbc_sha256':sha(llbc),'expected_work':'Aeneas translation of pinned LLBC containing actual field reader + actual WideExact decoder; no build/re-extraction'}
(run/'command.json').write_text(json.dumps(command,indent=2)+'\n'); (run/'environment.json').write_text(json.dumps({'PATH':env['PATH']},indent=2)+'\n')
before=(cg/'memory.events').read_text(); start=time.monotonic(); timed=False
with (run/'stdout.log').open('x') as out:
 proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(run/'time.log'),*argv],cwd=W,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
 while proc.poll() is None:
  if time.monotonic()-start>300:
   timed=True; os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=3)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
   break
  time.sleep(.1)
status=proc.returncode; receipt={**command,'exit_status':status,'timed_out':timed,'wall_seconds':round(time.monotonic()-start,3),'swap_current_bytes':int((cg/'memory.swap.current').read_text()),'memory_peak_bytes':int((cg/'memory.peak').read_text()),'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'finished_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
t=(run/'time.log').read_text(); m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t); receipt['max_process_rss_kib']=int(m.group(1)) if m else None
if (gen/'translation.json').exists(): receipt['translation_sha256']=sha(gen/'translation.json'); receipt['generated_lean']={str(p.relative_to(run)):sha(p) for p in sorted(gen.rglob('*.lean'))}
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n'); print(json.dumps(receipt,indent=2)); sys.exit(status if status is not None else 1)
