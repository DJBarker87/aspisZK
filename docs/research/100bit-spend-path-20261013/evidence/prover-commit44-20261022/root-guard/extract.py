#!/usr/bin/env python3
"""Translate only the structural owned owner; no shipped-file mutation."""
import os,json,hashlib,subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit44-20261022')
CHARON='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
AENEAS='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
os.chdir(H/'root-guard')
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
 (H/(name+'-inputs.json')).write_text(json.dumps(dict(source_revision=(H/'revision.txt').read_text().strip(),hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(CHARON),Path(AENEAS),H/'root-guard/lib.rs']},reservations=caps),indent=2)+'\n')
 subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Optimized MIR compilation and isolated native root-guard diagnostic with BTreeMap internals opaque; no arithmetic execution','--',*cmd],check=True)
p=H/'extraction/rootguard44.llbc'
run('rootguard44-charon-v1',[CHARON,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','native_root_guard44::root_guard','--opaque','alloc::collections::btree::map','--dest-file',str(p),'--','--manifest-path',str(H/'root-guard/Cargo.toml'),'--offline','--release','--lib','--jobs','4'])
d=json.loads(p.read_text());assert d['has_errors'] is False
(H/'rootguard44-llbc.json').write_text(json.dumps(dict(has_errors=d['has_errors'],sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size_bytes=p.stat().st_size),indent=2)+'\n')
run('rootguard44-aeneas-v1',[AENEAS,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1RootGuard44','-dest',str(H/'extraction/generated'),'-subdir','AspisR1RootGuard44','-split-files','-emit-json',str(p)])
