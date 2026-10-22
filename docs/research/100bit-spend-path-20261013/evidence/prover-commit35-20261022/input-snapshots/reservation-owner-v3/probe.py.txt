#!/usr/bin/env python3
import os,json,hashlib,subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit35-20261022')
os.chdir(H/'ledger-probe')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(H/'probe-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
caps=[]
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
 try:
  v=p.read_text().strip()
  if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
 except OSError:pass
assert sum(x['bytes'] for x in caps)+8*2**30<=55*2**30,caps
(H/'ledger-probe-inputs.json').write_text(json.dumps(dict(source_revision=(H/'revision.txt').read_text().strip(),hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (H/'ledger-probe').iterdir() if p.is_file()},reservations=caps),indent=2)+'\n')
for name,cmd,note in [('ledger-probe-compile-v1',['cargo','build','--release','--offline','-j','4'],'Optimized compilation of verbatim native durable store with real std and pinned sha2; no arithmetic gate'),('ledger-probe-run-v1',[str(H/'probe-target/release/ledger-probe35'),str(H/'retained-probe-ledger')],'Two create_new outcomes on distinct nonce paths from the same retained ledger; fixed public test nonces, no wallet keys')]:
 subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),note,'--',*cmd],check=True)
