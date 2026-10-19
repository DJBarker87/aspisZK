from pathlib import Path
import argparse,hashlib,json,os,re,signal,subprocess,time
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--attempt',required=True);a.add_argument('--phase',required=True);opts=a.parse_args();w=opts.root;source=w/'source'
os.umask(0o077)
commands=json.loads((w/'artifact-plan.json').read_text())

cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']};assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'},limits
cmd=commands[opts.phase];out=w/'runs'/opts.attempt;out.mkdir(parents=True,exist_ok=False)
env=dict(os.environ);env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-r1-worker-b-1h-native-20261019/cargo-target')
if opts.phase!='sbf':env['RUSTUP_TOOLCHAIN']='stable'
else:env.pop('RUSTUP_TOOLCHAIN',None);env['CARGO_TARGET_DIR']='/home/dombarker/project-offloads/aspis-r1-decision1h-20261019/sbf-target'
for k in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS']:env.pop(k,None)
record=dict(source_revision='5c63b0bba7ceae70bad1f980a766fa65728624fc',source_archive_sha256='5d8cf790ac1eb83c7328a270b2398d908ae6f3b474a4d3d50c4ae71a5a8affe4',command=cmd,cwd=str(source),expected_time='Optimized compilation/link and native source-equivalence verification; no proof generation or arithmetic elimination',env={k:env.get(k) for k in ['PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR']},limits=limits,runner_sha256=sha(__file__))
# Record exact checked source files instead of attributing old artifacts to new bodies.
record['artifact_sha256']={str(p):sha(p) for p in [w/'artifacts/aspis_r1_cost_probe_program.so',Path('/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/evidence/gate-bin/pool_gate-candidate-asq8-stage1log')]}
record['changed_source_sha256']={str(f.relative_to(source)):sha(f) for f in [source/'crates/aspis-r1-cost-probe/src/r1_wire.rs',source/'crates/aspis-r1-cost-probe/src/r1_semantic.rs',source/'crates/aspis-r1-cost-probe/src/verifier.rs']}
(out/'command.json').write_text(json.dumps(record,indent=2)+'\n');start=time.monotonic();peak=0;stop=None;before=(cg/'memory.events').read_text()
with (out/'stdout.log').open('x') as log:
 p=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  peak=max(peak,int((cg/'memory.current').read_text()))
  if time.monotonic()-start>600:
   stop='Mandatory ten-minute progress review';os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=3)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
   break
  time.sleep(.5)
 p.wait()
t=(out/'time.log').read_text()
def number(label):
 m=re.search(re.escape(label)+r':\s*(\d+)',t);return int(m[1]) if m else None
record.update(exit_status=p.returncode,wall_seconds=round(time.monotonic()-start,3),peak_process_rss_kib=number('Maximum resident set size (kbytes)'),process_swaps=number('Swaps'),sampled_cgroup_peak_bytes=peak,cgroup_swap_current=int((cg/'memory.swap.current').read_text()),memory_events_before=before,memory_events_after=(cg/'memory.events').read_text(),stopped_reason=stop,print_axioms='N/A: native Rust/SBF build or gate, no Lean proof')
(out/'receipt.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True);raise SystemExit(p.returncode)
