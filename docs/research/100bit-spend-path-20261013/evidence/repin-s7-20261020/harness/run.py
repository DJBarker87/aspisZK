#!/usr/bin/env python3
import os,json,hashlib,subprocess,sys
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-repin-s7-20261020')
phase=sys.argv[1]
p=json.loads((H/(phase+'-input.json')).read_text())
for path,expected in p['tool_pins'].items():
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==expected,path
for path,expected in p['source_hashes'].items():
 assert hashlib.sha256((H/'src'/path).read_bytes()).hexdigest()==expected,path
env=dict(os.environ)
env.update(RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(H/'charon-target'),RUSTFLAGS='-C link-arg=-Wl,--threads=4')
for k in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(k,None)
raise SystemExit(subprocess.call([str(H/'harness/capped-run.sh'),'extract-'+phase+'-current-owners','Compilation and pinned '+phase+' lowering only; no arithmetic release gate',str(H/'src'),'--',*p['command']],env=env))
