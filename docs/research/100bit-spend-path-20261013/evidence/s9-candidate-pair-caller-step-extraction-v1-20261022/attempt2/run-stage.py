from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time,re
W=Path(__file__).resolve().parent
assert sys.argv[1]=='aeneas'
G=1024**3;inp=W/'input';cut=inp/'source-cut';pins=json.loads((inp/'sourcecut-pins.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,want in pins['source_cut_files'].items():assert sha(cut/n)==want,n
llbc=W/'reused-charon/charon/pair-caller-step.llbc'; origin=json.loads((W/'reused-charon/origin.json').read_text())
assert sha(llbc)==origin['llbc_sha256']
obj=json.loads(llbc.read_text());assert not obj.get('has_errors')
tools=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016');aeneas=tools/'bin/aeneas';charon=tools/'charon-target/release/charon'
toolpins={str(aeneas):'959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3',str(charon):'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'}
for p,h in toolpins.items():assert sha(Path(p))==h,p
cgline=Path('/proc/self/cgroup').read_text().strip();assert cgline.startswith('0::'),cgline;cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')};assert limits=={'memory.high':str(2*G),'memory.max':str(4*G),'memory.swap.max':'0'},limits
run=W/'runs/aeneas';run.mkdir(parents=True,exist_ok=False);gen=run/'generated'
cmd=[str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1S9PairCallerStepV1','-dest',str(gen),'-subdir','AspisR1S9PairCallerStepV1','-split-files','-emit-json',str(llbc)]
cwd=cut;env=os.environ.copy();env.update({'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'})
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS'):env.pop(k,None)
command={'phase':'aeneas','argv':cmd,'cwd':str(cwd),'limits':limits,'cgroup':str(cg),'tool_pins':toolpins,'candidate_weights_sha256':pins['candidate_weights_sha256'],'frozen_weights_sha256':pins['frozen_weights_sha256'],'sourcecut_pins_sha256':sha(inp/'sourcecut-pins.json'),'reused_llbc_sha256':sha(llbc),'expected_work':'Aeneas translation of the inspected caller-step LLBC; no compiler or toolchain rebuild','started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
(run/'command.json').write_text(json.dumps(command,indent=2)+'\n');(run/'environment.json').write_text(json.dumps({'PATH':env['PATH']},indent=2)+'\n');before=(cg/'memory.events').read_text();start=time.monotonic();timed=False
with (run/'stdout.log').open('x') as o:
 proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(run/'time.log'),*cmd],cwd=cwd,env=env,stdout=o,stderr=subprocess.STDOUT,start_new_session=True)
 while proc.poll() is None:
  if time.monotonic()-start>180:
   timed=True;os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=3)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
   break
  time.sleep(.1)
status=proc.returncode;wall=time.monotonic()-start;receipt={**command,'exit_status':status,'timed_out':timed,'wall_seconds':round(wall,3),'swap_current_bytes':int((cg/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'finished_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
t=(run/'time.log').read_text();m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t);receipt['peak_process_rss_kib']=int(m.group(1)) if m else None
if (gen/'translation.json').exists():
 receipt['outputs']={'translation.json':sha(gen/'translation.json')};receipt['generated_files']={str(p.relative_to(run)):sha(p) for p in sorted(gen.rglob('*.lean'))};receipt['source_function_present']={n:(n in (gen/'AspisR1S9PairCallerStepV1/Funs.lean').read_text()) for n in ('pair_step_root','pair_s2_libra_parts_projection','factored_s2_libra_weights')}
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(status if status is not None else 1)
