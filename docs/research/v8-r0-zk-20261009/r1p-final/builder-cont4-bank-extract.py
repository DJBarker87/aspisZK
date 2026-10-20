#!/usr/bin/env python3
"""Focused extraction of the two actual structural glue functions."""
import fcntl, hashlib, json, os, pathlib, subprocess, time
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref4-20261021')
T=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
lock=(R/'rust-worker.lock').open('w'); fcntl.flock(lock,fcntl.LOCK_EX)
E=R/'continuation4/bank-extraction'; E.mkdir(exist_ok=False)
(E/'generated').mkdir()
env=os.environ.copy(); env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
 RUSTUP_TOOLCHAIN='nightly-2026-06-01',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4',
 CARGO_TARGET_DIR=str(R/'public-extraction-target'))
def reserve():
 while True:
  reserved=0
  for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
   try:
    v=p.read_text().strip()
    if v!='max' and (p.parent/'cgroup.procs').read_text().strip(): reserved+=int(v)
   except OSError: pass
  if reserved+8*2**30<=55*2**30: return
  print('public extraction reservation hold',reserved,flush=True); time.sleep(20)
def run(name,cmd):
 reserve()
 print(name,'expected: focused compilation/translation of structural glue, no arithmetic release gate',flush=True)
 rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G',
  '-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'stage0/capped.py'),str(E/name),
  'Focused structural glue compilation/translation','--','timeout','180',*cmd],
  cwd=R/'source',env=env).returncode
 print(name,'exit',rc,flush=True)
 print((E/name/'stdout.log').read_text()[-2000:],flush=True)
 print((E/name/'stderr.log').read_text()[-2000:],flush=True)
 return rc
cmd=[str(T/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built']
for fn in ['merged_banks']:
 cmd+=['--start-from','crate::pool_v1::pair_forest_copy_builder::'+fn]

for dep in ['aspis_r0_block_writer_copies::*','aspis_r0_poseidon_copy::*']:
 cmd+=['--include',dep]
cmd+=['--dest-file',str(E/'glue.llbc'),'--','--lib','-p','aspis-statement','--release','--offline','-j','4']
rc=run('charon',cmd)
if rc==0:
 rc=run('aeneas',[str(T/'bin/aeneas'),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean',
  '-namespace','AspisBuilderGlueSource','-dest',str(E/'generated'),'-loops-to-rec','-print-unknown-externals',str(E/'glue.llbc')])
pins={str(p.relative_to(R/'source')):hashlib.sha256(p.read_bytes()).hexdigest()
 for root in ['crates/aspis-core','crates/aspis-statement']
 for p in (R/'source'/root).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml']}
(E/'pins.json').write_text(json.dumps({'sources':pins,'tools':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()
 for p in [T/'charon-target/release/charon',T/'bin/aeneas']},'exit':rc},indent=2)+'\n')
raise SystemExit(rc)
