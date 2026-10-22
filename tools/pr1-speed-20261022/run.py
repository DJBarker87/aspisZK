#!/usr/bin/env python3
from pathlib import Path
import subprocess,os,sys
r=Path(__file__).resolve().parents[2];h=r.parent
name=sys.argv[1];cmd=sys.argv[2:]
# Cargo may reuse path-dependency fingerprints across copied source snapshots.
# Invalidate project source mtimes when compiling; preserve registry caches.
if cmd and cmd[0]=='cargo':
 for base in ['crates','programs','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3','tools/pr1-speed-20261022']:
  for p in (r/base).rglob('*'):
   if p.is_file() and (p.suffix=='.rs' or p.name=='Cargo.toml'):os.utime(p,None)
subprocess.run(['python3',str(r/'tools/pr1-speed-20261022/admission.py'),str(r/('reservation-'+name+'.json'))],check=True)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_TARGET_DIR=str(h/'pr1-target'))
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(r/'tools/pr1-speed-20261022/receipt.py'),name,*cmd],cwd=r,env=env).returncode)
