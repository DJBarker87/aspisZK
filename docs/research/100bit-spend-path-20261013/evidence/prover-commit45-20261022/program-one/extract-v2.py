#!/usr/bin/env python3
"""Translate only the structural owned owner; no shipped-file mutation."""
import os,json,hashlib,subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit45-20261022')
CHARON='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
AENEAS='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
os.chdir(H/'program-one')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(H/'charon-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
(H/'extraction').mkdir(exist_ok=True)
def run(name,cmd):
 caps=[]
 for p in Path('/sys/fs/cgroup').rglob('memory.max'):
  try:
   v=p.read_text().strip()
   if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
  except OSError:pass
 assert sum(x['bytes'] for x in caps)+8*2**30<=55*2**30,caps
 (H/(name+'-inputs.json')).write_text(json.dumps(dict(source_revision=(H/'revision.txt').read_text().strip(),hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(CHARON),Path(AENEAS),H/'program-one/lib.rs']},reservations=caps),indent=2)+'\n')
 subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Optimized MIR compilation and isolated native program-one diagnostic with BTreeMap internals opaque; no arithmetic execution','--',*cmd],check=True)
p=H/'extraction/programone45-v2.llbc'
run('programone45-charon-v2',[CHARON,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','native_program_one45::program','--opaque','alloc::collections::btree::map','--opaque','core::cell','--opaque','native_program_one45::concat','--dest-file',str(p),'--','--manifest-path',str(H/'program-one/Cargo.toml'),'--offline','--release','--lib','--jobs','4'])
d=json.loads(p.read_text());assert d['has_errors'] is False
(H/'programone45-v2-llbc.json').write_text(json.dumps(dict(has_errors=d['has_errors'],sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size_bytes=p.stat().st_size),indent=2)+'\n')
run('programone45-aeneas-v2',[AENEAS,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1ProgramOne45','-dest',str(H/'extraction/generated'),'-subdir','AspisR1ProgramOne45','-split-files','-emit-json',str(p)])
