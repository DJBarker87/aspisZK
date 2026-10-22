#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, signal, subprocess, sys, time
HERE=Path(__file__).resolve().parent
CFG=json.loads((HERE/'config.json').read_text())
assert len(sys.argv)==2 and sys.argv[1] in ('charon','aeneas','lean','proof','proof-v2','proof-v3','proof-v4','proof-v5','proof-v6')
phase=sys.argv[1]; G=1024**3; high=int(CFG['scope_memory_high_bytes']); cap=int(CFG['scope_memory_max_bytes'])
cgline=Path('/proc/self/cgroup').read_text().strip(); assert cgline.startswith('0::')
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max')}
assert limits=={'memory.high':str(high),'memory.max':str(cap),'memory.swap.max':'0'},limits
workspace=Path(CFG['source_workspace'])
sources=[workspace/'Cargo.toml',workspace/'Cargo.lock',workspace/'src/lib.rs']
hashes={str(p.relative_to(workspace)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
assert hashes['src/lib.rs']=='ac32d53f3b31cbf21818c0d369ccf93c86116a28479723071d54c608b82e0184'
for t,k in ((CFG['charon'],'charon_sha256'),(CFG['aeneas'],'aeneas_sha256')):
 assert Path(t).is_file() and hashlib.sha256(Path(t).read_bytes()).hexdigest()==CFG[k],t
outroot=Path(CFG['output_root']); run=outroot/('runs-'+phase); run.mkdir(parents=True,exist_ok=False)
env=dict(os.environ); env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=CFG['target_dir'])
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH'): env.pop(k,None)
if phase=='charon':
 target=outroot/'candidate.llbc'
 commands=[[CFG['charon'],'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--start-from','crate::from_limbs_entry','--dest-file',str(target),'--','--manifest-path',str(workspace/'Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1']]
else:
 llbc=outroot/'candidate.llbc'; assert llbc.is_file() and hashlib.sha256(llbc.read_bytes()).hexdigest()=='19b1bb1b6b21ee214dbde37305754a83305892f6aa54cb0f222d6463eee4b859'
 if phase=='aeneas':
  target=outroot/'generated'
  commands=[[CFG['aeneas'],'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1CheckedQCandidateV1','-dest',str(target),'-subdir','AspisR1CheckedQCandidateV1','-split-files','-emit-json',str(llbc)]]
 else:
  lean=CFG['lean']; generated=outroot/'generated'; leanSrc=Path(CFG['lean_source']); objects=Path(CFG['lean_objects']); objects.mkdir(parents=True,exist_ok=True)
  (objects/'AspisR1CheckedQCandidateV1').mkdir(parents=True,exist_ok=True)
  closure=json.loads(Path(CFG['base_preflight']).read_text())['lean_path']
  env['LEAN_PATH']=str(CFG['lean_objects'])+':'+closure
  commands=[[lean,'-j1','-M4400','-R',str(leanSrc),'-o',str(objects/'AspisR1CheckedQCandidateV1/Types.olean'),str(leanSrc/'AspisR1CheckedQCandidateV1/Types.lean')],
   [lean,'-j1','-M4400','-R',str(leanSrc),'-o',str(objects/'AspisR1CheckedQCandidateV1/Funs.olean'),str(leanSrc/'AspisR1CheckedQCandidateV1/Funs.lean')],
   [lean,'-j1','-M4400','-R',str(Path(CFG['lean_probe'])),'-o',str(objects/'CandidateAllEquivalence.olean'),str(Path(CFG['lean_probe'])/'CandidateAllEquivalence.lean')]]
  if phase in ('proof-v2','proof-v3','proof-v4','proof-v5','proof-v6'): commands=commands[-1:]
(run/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
(run/'environment.json').write_text(json.dumps({k:env.get(k) for k in ('PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','LEAN_PATH')},indent=2)+'\n')
(run/'source-pins.json').write_text(json.dumps(hashes,indent=2)+'\n')
before=(cg/'memory.events').read_text(); started=time.monotonic(); peak=0; results=[]
for n,cmd in enumerate(commands):
 name=f'target-{n+1}'; timing=run/(name+'.time.log'); logpath=run/(name+'.log')
 with logpath.open('x') as log:
  p=subprocess.Popen(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=workspace,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  t0=time.monotonic(); timeout=False
  while p.poll() is None:
   peak=max(peak,int((cg/'memory.current').read_text()))
   if time.monotonic()-t0>180:
    timeout=True; os.killpg(p.pid,signal.SIGTERM)
    try:p.wait(timeout=3)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
    break
   time.sleep(.1)
  p.wait()
 results.append({'command':cmd,'exit_status':p.returncode,'timed_out':timeout,'timing_log':str(timing),'log':str(logpath)})
 if p.returncode!=0 or timeout: break
outputs={}
for ofile in (outroot/'generated').rglob('*'):
 if ofile.is_file(): outputs[str(ofile.relative_to(outroot))]=hashlib.sha256(ofile.read_bytes()).hexdigest()
if phase in ('lean','proof'):
 for ofile in Path(CFG['lean_objects']).rglob('*.olean'):
  outputs[str(ofile)]=hashlib.sha256(ofile.read_bytes()).hexdigest()
receipt={'phase':phase,'targets':results,'exit_status':p.returncode,'wall_seconds':time.monotonic()-started,
 'sampled_cgroup_peak_bytes':peak,'scope_memory_events_before':before,'scope_memory_events_after':(cg/'memory.events').read_text(),
 'scope_memory_peak_cumulative':int((cg/'memory.peak').read_text()),'scope_swap_current':int((cg/'memory.swap.current').read_text()),
 'limits':limits,'source_revision_at_launch':'hash-pinned isolated source cut; no git metadata','source_hashes':hashes,
 'outputs':outputs,'source_workspace':str(workspace),'target_dir':CFG['target_dir'],'scope':CFG['unit'],
 'classification':'candidate-only; selected emitted-body proof setup, no frozen production claim'}
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n'); print(json.dumps(receipt),flush=True); raise SystemExit(p.returncode)
