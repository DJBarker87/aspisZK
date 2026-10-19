#!/usr/bin/env python3
"""Three-stage capped run for the isolated one-token move-closure candidate."""
import hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
ATTEMPT=Path(__file__).resolve().parent
KIT=ATTEMPT/'input'
BASE=ATTEMPT.parent/'attempt-d'/'input'
TARGET=ATTEMPT.parent/'attempt-d'/'target'
RUSTUP=Path('/home/dombarker/.cargo/bin/rustup')
CARGO=Path('/home/dombarker/.cargo/bin/cargo')
CHARON=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
AENEAS=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas')
TOOLCHAIN='nightly-2026-06-01'
LIMITS={'MemoryHigh':'4G','MemoryMax':'6G','MemorySwapMax':'0','TasksMax':'128'}
ENV={**os.environ,'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',
     'RUSTUP_TOOLCHAIN':TOOLCHAIN,'CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OPT_LEVEL':'3',
     'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes',
     'CARGO_TARGET_DIR':str(TARGET),'CARGO_NET_OFFLINE':'true'}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def preflight():
 if not KIT.is_dir() or not BASE.is_dir():raise SystemExit('missing candidate/base input')
 man=json.loads((KIT/'merged-source-manifest.json').read_text())
 rows={r['merged_path']:r for r in man['source_files']}
 mismatch=[]
 for rel,row in rows.items():
  p=KIT/rel
  if not p.is_file() or sha(p)!=row['sha256']:mismatch.append(rel)
 if mismatch:raise SystemExit('candidate manifest mismatch: '+repr(mismatch[:20]))
 rel='src/statement/state_only_poseidon.rs'
 cand=(KIT/rel).read_bytes(); base=(BASE/rel).read_bytes()
 old=b'let raw = core::array::from_fn(|limb| {'; new=b'let raw = core::array::from_fn(move |limb| {'
 if base.count(old)!=2 or cand.count(new)!=1 or cand.count(old)!=1:raise SystemExit('candidate is not the unique first-closure move edit')
 if cand.replace(new,old,1)!=base:raise SystemExit('candidate differs beyond one move token')
 for f in ['Cargo.toml','Cargo.lock','build.rs']:
  if sha(KIT/f)!=sha(BASE/f):raise SystemExit('scaffold/lock changed: '+f)
 cargo=subprocess.run([str(CARGO),'metadata','--manifest-path',str(KIT/'Cargo.toml'),'--no-deps','--format-version','1','--offline'],cwd=KIT,env=ENV,check=True,stdout=subprocess.PIPE,text=True).stdout
 (ATTEMPT/'cargo-metadata.json').write_text(cargo+'\n')
 rustc=subprocess.check_output([str(RUSTUP),'run',TOOLCHAIN,'rustc','--version','--verbose'],text=True)
 if '1.98.0-nightly' not in rustc or '14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' not in rustc:raise SystemExit('rustc pin mismatch')
 for p,h in [(CHARON,'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'),(AENEAS,'959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3')]:
  if sha(p)!=h:raise SystemExit('tool hash mismatch '+str(p))
 (ATTEMPT/'preflight.json').write_text(json.dumps({'candidate_manifest_sha256':sha(KIT/'merged-source-manifest.json'),'baseline_manifest_sha256':sha(BASE/'merged-source-manifest.json'),'baseline_modified_file_sha256':sha(BASE/rel),'candidate_modified_file_sha256':sha(KIT/rel),'one_token_candidate_verified':True,'cargo_lock_unchanged':True,'source_files':len(rows),'rustc':rustc,'charon_sha256':sha(CHARON),'aeneas_sha256':sha(AENEAS),'reused_target_dir':str(TARGET)},indent=2)+'\n')
 (ATTEMPT/'environment.json').write_text(json.dumps({k:ENV[k] for k in ['RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_PROFILE_RELEASE_OPT_LEVEL','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','RUSTFLAGS','CARGO_TARGET_DIR','CARGO_NET_OFFLINE']},indent=2)+'\n')

def inside():
 name=sys.argv[2]; cmd=json.loads(sys.argv[3]); log=ATTEMPT/'logs'/f'{name}.log'; recp=ATTEMPT/'receipts'/f'{name}.json'
 log.parent.mkdir(exist_ok=True);recp.parent.mkdir(exist_ok=True)
 start=time.monotonic(); wall=time.time()
 with log.open('x') as f:p=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=KIT,env=ENV,stdout=f,stderr=subprocess.STDOUT)
 elapsed=time.monotonic()-start
 cg=''
 for line in Path('/proc/self/cgroup').read_text().splitlines():
  if line.startswith('0::'):cg=line[3:];break
 cgroot=Path('/sys/fs/cgroup')/cg.lstrip('/')
 def read(k):
  try:return(cgroot/k).read_text().strip()
  except:return None
 t=log.read_text(errors='replace');mr=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',t);mw=re.search(r'Elapsed \(wall clock\) time .*?:\s*([0-9:.]+)',t)
 rec={'stage':name,'command':cmd,'exit_status':p.returncode,'wall_seconds_monotonic':round(elapsed,3),'usr_bin_time_wall':mw.group(1) if mw else None,'peak_process_rss_kib':int(mr.group(1)) if mr else None,'cgroup':cg,'cgroup_memory_peak_bytes':read('memory.peak'),'cgroup_memory_swap_peak_bytes':read('memory.swap.peak'),'cgroup_memory_swap_current_bytes':read('memory.swap.current'),'cgroup_memory_events':read('memory.events'),'cgroup_memory_high':read('memory.high'),'cgroup_memory_max':read('memory.max'),'cgroup_memory_swap_max':read('memory.swap.max'),'cgroup_pids_max':read('pids.max'),'declared_scope_limits':LIMITS,'scope':'systemd user scope, sequential stages','time_started_unix':wall,'candidate_manifest_sha256':sha(KIT/'merged-source-manifest.json'),'runner_sha256':sha(Path(__file__))}
 recp.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);sys.exit(p.returncode)
if __name__=='__main__':
 if len(sys.argv)>1 and sys.argv[1]=='inside':inside()
 if ATTEMPT.exists() and any(ATTEMPT.iterdir()) and not KIT.exists():raise SystemExit('refuse unexpected populated attempt')
 preflight();(ATTEMPT/'output').mkdir(exist_ok=True)
 cmds={
 'build':[str(CARGO),'build','--manifest-path',str(KIT/'Cargo.toml'),'--package','aspis-r1-mask-extraction-probe','--features','r0,pool-v1-kernel','--no-default-features','--release','--locked','--offline','--lib'],
 'charon':[str(CHARON),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::extraction_probe::terminal_qm31_probe','--dest-file',str(ATTEMPT/'output/Terminal.llbc'),'--','--manifest-path',str(KIT/'Cargo.toml'),'--package','aspis-r1-mask-extraction-probe','--features','r0,pool-v1-kernel','--no-default-features','--release','--lib','--locked','--offline'],
 'aeneas':[str(AENEAS),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1SelectedMaskProbe','-dest',str(ATTEMPT/'output/generated'),'-subdir','AspisR1SelectedMaskProbe','-split-files','-emit-json','-print-unknown-externals','-loops-to-rec',str(ATTEMPT/'output/Terminal.llbc')]}
 for name,cmd in cmds.items():
  base=['systemd-run','--user','--scope','--quiet','--unit='+f'aspis-terminal-e-move-{name}-20261016']
  for k,v in LIMITS.items():base+=['--property='+k+'='+v]
  base += [sys.executable,str(Path(__file__).resolve()),'inside',name,json.dumps(cmd,separators=(',',':'))]
  outer=subprocess.run(base,cwd=ATTEMPT,env=ENV,text=True,capture_output=True,timeout=360)
  (ATTEMPT/'scope-launches').mkdir(exist_ok=True)
  (ATTEMPT/'scope-launches'/f'{name}.json').write_text(json.dumps({'stage':name,'systemd_run_argv':base,'exit_status':outer.returncode,'stdout':outer.stdout,'stderr':outer.stderr,'scope_limits':LIMITS},indent=2)+'\n')
  print(json.dumps({'stage':name,'exit_status':outer.returncode,'stdout':outer.stdout,'stderr':outer.stderr}),flush=True)
  if outer.returncode:raise SystemExit(outer.returncode)
 print('all candidate stages exited zero')
