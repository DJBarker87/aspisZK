#!/usr/bin/env python3
"""Host-only pinned extraction of the actual correspondence reference."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
R=Path(__file__).resolve().parents[2];version=sys.argv[2] if len(sys.argv)>2 else 'v6'
O=R/('extraction-reference-'+version);O.mkdir(exist_ok=True)
C=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
pins={str(C):'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',str(C.with_name('charon-driver')):'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45',str(A):'4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'}
for p,h in pins.items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h
phase=sys.argv[1]
if phase=='charon':
 cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default']
 for path in ['core::option::Option','core::result::Result','core::option::_::map','core::option::_::ok_or','core::result::_::map_err']:cmd+=['--include',path]
 for path in ['body_byte','decode_k_spec','decode_e_spec']:cmd+=['--start-from','crate::'+path]
 for path in ['aspis_core::field','aspis_core::r0::heap','aspis_core::circle::SecureCirclePoint','aspis_r1_cost_probe::transport::Variant','aspis_r1_cost_probe::verifier::Prepared','aspis_r1_cost_probe::verifier::Accumulator','aspis_r1_cost_probe::verifier::Error']:cmd+=['--include',path]
 cmd+=['--dest-file',str(O/'CheckpointAbi2.llbc'),'--','--manifest-path',str(R/'tools/oracle-port-ckpt-abi2/Cargo.toml'),'--offline','--release','--lib','--jobs','4']
else:
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','OraclePortCkptAbi2Extracted','-dest',str(O/'generated'),'-subdir','OraclePortCkptAbi2Extracted','-split-files','-emit-json',str(O/'CheckpointAbi2.llbc')]
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='4',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(R/'charon-target'),CARGO_NET_OFFLINE='true',RUSTFLAGS='--cfg aeneas_ref -C link-arg=-Wl,--threads=4')
for n in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(n,None)
(O/(phase+'-command.json')).write_text(json.dumps(dict(command=cmd,tool_pins=pins,source_sha256=hashlib.sha256((R/'tools/oracle-port-ckpt-abi2/src/lib.rs').read_bytes()).hexdigest()),indent=2)+'\n')
subprocess.run(['python3',str(R/'tools/oracle-port-ckpt-abi2/reservation.py'),str(R/('reservation-'+phase+'.json'))],check=True,stdout=subprocess.DEVNULL)
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','tools/oracle-port-ckpt-abi2/host-run.py',phase+'-reference-'+version,'timeout','240',*cmd],cwd=R,env=env).returncode)
