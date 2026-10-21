#!/usr/bin/env python3
"""Extract the owned expander reference; stops on any invalid lowering."""
import os,sys,json,hashlib,subprocess,time,fcntl
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit13-20261021')
CHARON='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
AENEAS='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
worker_lock=(H/'extract-worker.lock').open('a')
fcntl.flock(worker_lock,fcntl.LOCK_EX)
os.chdir(H/'src')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(H/'charon-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4 --cfg aeneas_ref')
def run(name,cmd):
 while True:
  caps=[]
  for p in Path('/sys/fs/cgroup').rglob('memory.max'):
   try:
    v=p.read_text().strip()
    if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
   except OSError:pass
  if sum(x['bytes'] for x in caps)+8*2**30<=55*2**30: break
  print('Reservation hold',flush=True);time.sleep(30)
 pins=dict(source_hashes={str(p.relative_to(H/'src')):hashlib.sha256(p.read_bytes()).hexdigest() for p in (H/'src').rglob('*.rs')},source_revision=(H/'revision.txt').read_text().strip(),reservations=caps,sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(CHARON),Path(AENEAS),H/'src/crates/aspis-prover/src/prover_commit_reference.rs']})
 (H/(name+'-inputs.json')).write_text(json.dumps(pins,indent=2)+'\n')
 rc=subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Optimized compilation and owned reference translation; no dense arithmetic','--',*cmd]).returncode
 if rc:raise SystemExit(rc)
(H/'extraction').mkdir(exist_ok=True)
run('material-charon-v2',[CHARON,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::state_only_hiding::build_mask_material_for_layout',
 '--opaque','aspis_prover::state_only_hiding::{aspis_prover::state_only_hiding::SeedExpander}::m31',
 '--opaque','aspis_prover::state_only_hiding::{aspis_prover::state_only_hiding::SeedExpander}::qm31',
 '--opaque','crate::state_only_hiding::balance_m31_copy_inactive',
 '--opaque','crate::state_only_hiding::balance_qm31_copy_inactive',
 '--include','core::result::Result','--include','aspis_core::field::M31','--include','aspis_core::field::CM31','--include','aspis_core::field::QM31','--include','aspis_core::state_only_hiding::StateOnlyHidingContext','--include','aspis_core::state_only_hiding::{_}::encode','--include','aspis_statement::TraceCell',
 '--opaque','aspis_core','--opaque','aspis_statement','--dest-file',str(H/'extraction/ProverMaterial13-v2.llbc'),'--','--manifest-path',str(H/'src/crates/aspis-prover/Cargo.toml'),'--locked','--offline','--release','--lib','--features','r0','--jobs','4'])
p=H/'extraction/ProverMaterial13-v2.llbc';data=json.loads(p.read_text());(H/'material-llbc-v2.json').write_text(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size_bytes=p.stat().st_size,has_errors=data.get('has_errors')),indent=2)+'\n')
assert data['has_errors'] is False
run('material-aeneas-v2',[AENEAS,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1ProverMaterial13','-dest',str(H/'extraction/generated-v2'),'-subdir','AspisR1ProverMaterial13','-split-files','-emit-json',str(p)])
