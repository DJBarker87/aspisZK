#!/usr/bin/env python3
"""Pinned extraction preflight for exact owned parser range reference."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-s2-kani-20261021')
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
phase=sys.argv[1]; attempt=sys.argv[2]; out=H/'parser-extraction';out.mkdir(exist_ok=True)
llbc=out/'S2Parser.llbc'
if phase=='charon':
 cmd=[str(T/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::record_range','--dest-file',str(llbc),'--','--manifest-path',str(H/'reference-parser/Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 assert not json.loads(llbc.read_text())['has_errors']
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisS2ParserRef','-dest',str(out/'generated'),'-subdir','AspisS2ParserRef','-split-files','-emit-json',str(llbc)]
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(H/'charon-target'),CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
for n in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(n,None)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
(out/(phase+'-input.json')).write_text(json.dumps({'command':cmd,'source_sha256':sha(H/'reference-parser/src/lib.rs'),'tools':{str(p):sha(p) for p in [A,T/'charon-target/release/charon',T/'charon-target/release/charon-driver']},'environment':{k:env[k] for k in ['RUSTUP_TOOLCHAIN','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','RUSTFLAGS']}},indent=2)+'\n')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/('reservation-parser-'+phase+'.json'))],check=True,stdout=subprocess.DEVNULL)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/('receipts/parser-'+phase+'-'+attempt)),'Pinned '+phase+' translation of owned parser range reference; no arithmetic execution','--',*cmd],env=env))
