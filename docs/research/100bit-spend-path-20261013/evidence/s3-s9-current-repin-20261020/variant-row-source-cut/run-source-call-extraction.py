from pathlib import Path
import argparse,hashlib,json,os,re,signal,subprocess,time
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n')
a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--phase',choices=['charon','aeneas'],required=True);opts=a.parse_args()
w=opts.root;kit=w/'input';plan=json.loads((kit/'command-plan.json').read_text());pins=json.loads((kit/'source-pins.json').read_text())
for f,h in pins['kit_file_sha256'].items():assert sha(kit/f)==h,f
for f,h in [(plan['tools']['charon'],plan['tools']['charon_sha256']),(str(Path(plan['tools']['charon']).with_name('charon-driver')),plan['tools']['charon_driver_sha256']),(plan['tools']['aeneas'],plan['tools']['aeneas_sha256'])]:assert sha(f)==h,f
cgline=Path('/proc/self/cgroup').read_text().strip();assert cgline.startswith('0::')
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
assert limits=={'memory.high':str(plan['scope_memory_high_bytes']),'memory.max':str(plan['scope_memory_max_bytes']),'memory.swap.max':'0'},limits
out=w/'runs'/(opts.phase+'-a');out.mkdir(parents=True,exist_ok=False)
llbc_name=Path(plan['charon_command'][plan['charon_command'].index('--dest-file')+1]).name
cmd=[v.replace(plan['kit_dir'],str(w)) for v in plan[opts.phase+'_command']]
if opts.phase=='charon':cmd[cmd.index('--dest-file')+1]=str(w/llbc_name)
else:
 cmd[cmd.index('-dest')+1]=str(w/'generated')
 cmd[-1]=str(w/llbc_name)
if opts.phase=='aeneas':
 prior=json.loads((w/'runs/charon-a/receipt.json').read_text());assert prior['exit_status']==0
 assert sha(w/llbc_name)==prior['outputs'][llbc_name]
env=dict(os.environ);env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN=plan['tools']['rustup_toolchain'],CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(w/'target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for key in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(key,None)
dump(out/'command.json',dict(command=cmd,cwd=str(kit),environment={k:env.get(k) for k in ['PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']},scope='Pinned current-source standalone declaration extraction; no Lean result or caller equivalence claimed.',expected_time='Rust release compilation and Charon source extraction' if opts.phase=='charon' else 'Aeneas translation of the pinned Charon IR',source_revision=pins['source_revision'],source_pins_sha256=sha(kit/'source-pins.json'),plan_sha256=sha(kit/'command-plan.json'),runner_sha256=sha(__file__),limits=limits))
start=time.monotonic();peak=0;stop=None;before=(cg/'memory.events').read_text()
with (out/'stdout.log').open('x') as log:
 p=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],cwd=kit,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  peak=max(peak,int((cg/'memory.current').read_text()))
  if time.monotonic()-start>180:
   stop='180 second scoped extraction timeout';os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=3)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
   break
  time.sleep(.2)
 p.wait()
outputs={}
if (w/llbc_name).is_file():outputs[llbc_name]=sha(w/llbc_name)
if (w/'generated').exists():
 for f in (w/'generated').rglob('*'):
  if f.is_file():outputs[str(f.relative_to(w))]=sha(f)
timing=(out/'time.log').read_text()
def number(label):
 m=re.search(re.escape(label)+r':\s*(\d+)',timing);return int(m[1]) if m else None
receipt=dict(phase=opts.phase,exit_status=p.returncode,wall_seconds=round(time.monotonic()-start,3),peak_process_rss_kib=number('Maximum resident set size (kbytes)'),process_swaps=number('Swaps'),sampled_cgroup_peak_bytes=peak,cgroup_swap_current=int((cg/'memory.swap.current').read_text()),memory_events_before=before,memory_events_after=(cg/'memory.events').read_text(),stopped_reason=stop,limits=limits,source_revision=pins['source_revision'],source_pins_sha256=sha(kit/'source-pins.json'),runner_sha256=sha(__file__),command=cmd,outputs=outputs,print_axioms='N/A: extraction only; no Lean compilation',scope='Current-source standalone extraction, no caller refinement claim.')
dump(out/'receipt.json',receipt);print(json.dumps(receipt),flush=True);raise SystemExit(p.returncode)
