#!/usr/bin/env python3
"""Focused extraction of the two actual public projection functions."""
import fcntl, hashlib, json, os, pathlib, subprocess, time
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref4-20261021')
T=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
lock=(R/'rust-worker.lock').open('w'); fcntl.flock(lock,fcntl.LOCK_EX)
E=R/'continuation4/admission-native'; E.mkdir(exist_ok=False)
(E/'generated').mkdir()
env=os.environ.copy(); env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
 RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4',
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
 print(name,'expected: optimized compilation then admission counterexample execution',flush=True)
 rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G',
  '-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'stage0/capped.py'),str(E/name),
  'Optimized admission-counterexample execution check; expected time in compilation','--','timeout','180',*cmd],
  cwd=R/'source',env=env).returncode
 print(name,'exit',rc,flush=True)
 print((E/name/'stdout.log').read_text()[-2000:],flush=True)
 print((E/name/'stderr.log').read_text()[-2000:],flush=True)
 return rc
cmd=['cargo','test','--manifest-path','tools/r1-builder-reference/Cargo.toml','--release','--offline','-j','4','--test','noncanonical_outputs']
rc=run('native',cmd)
raise SystemExit(rc)
