#!/usr/bin/env python3
"""Same complete codec reference; include the three actual standard-library bodies."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-full-forest-codec-full-std-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in json.loads((P/'source-pins.json').read_text()).items():assert sha(P/n)==h,n
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
patterns=['core::array::equality::_::eq','core::option::_::ok_or','core::option::_::eq']
cmd=[str(T),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--include','aspis_statement::*','--include','aspis_core::field::*',*sum((['--include',p] for p in patterns),[]),'--start-from','crate::encode','--start-from','crate::decode','--dest-file',str(P/'Codec.llbc'),'--','--manifest-path',str(P/'input/Cargo.toml'),'--offline','--release','--lib','--jobs','1']
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
tag='s6-full-forest-codec-full-std-charon-v2';collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
inv=json.loads(subprocess.check_output(['python3',str(collector)],text=True));(H/(tag+'-global-admission.json')).write_text(json.dumps(inv,indent=2)+'\n')
assert inv['effective_sum_bytes']+2*2**30<=48*2**30 and inv['MemAvailable_kB']*1024>=4*2**30, 'Global admission denied'
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,tool_sha256=sha(T),source_pins_sha256=sha(P/'source-pins.json'),include_standard_patterns=patterns,qualification=__doc__,expected_time='Warm optimized cached Rust/Charon extraction, unchanged candidate bodies, three additional std definitions. Prior focused Charon used491MB RSS; explicit High1G/Max2G/Swap0.'),indent=2)+'\n')
os.chdir(P/'input');raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Include actual three std method bodies in native codec extraction','--','timeout','180',*cmd]))
