"""Pinned optimized Charon run; exact commands and frozen lock continuity recorded."""
from pathlib import Path
import subprocess,json,os,hashlib,sys
B=Path(__file__).resolve().parent;x=json.loads((B/sys.argv[1]).read_text());S=B/'NHA_scratch';shape=x['shape'];root=x['root'];stem=x['llbc_stem']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
C=B/'NHA_bin/charon';A=B/'NHA_bin/aeneas-b59d5188-extended'
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
lock=sha(S/'Cargo.lock');assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
cmd=[str(C),'cargo','--preset','aeneas','--mir',x.get('mir','built'),'--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--start-from',root]
if shape=='field':
 cmd+=['--opaque','crate::field::_']
 for ty in ['crate::field::M31','crate::field::CM31','crate::field::QM31']:cmd+=['--include',ty]
 package='aspis-core';features='r0'
elif shape=='queries':
 package='aspis-core';features='r0'
else:
 package='aspis-r1-cost-probe';features='private-leaf-salts,optimized-terminal,program-build'
 for mod in ['crate::transcript','crate::weights','crate::r1_semantic','crate::r1_wire','aspis_core::field','aspis_core::circle','crate::fast_pairing','crate::trace']:cmd+=['--opaque',mod+'::_']
 for ty in ['crate::transcript::Transcript','crate::r1_semantic::Verified','crate::r1_wire::SemanticTranscript','crate::r1_wire::Challenges','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::circle::SecureCirclePoint','crate::fast_pairing::EbyKDot','crate::fast_pairing::canonical::Dot']:cmd+=['--include',ty]
cmd+=['--dest-file',str(B/'NHA_inputs'/(stem+'.llbc')),'--','--manifest-path',str(S/'crates'/package/'Cargo.toml'),'--features',features,'--offline','--locked','--release','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NHA_charon_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Copt-level=3 -Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=S,env=env)
p=B/'NHA_inputs'/(stem+'.llbc')
pins=dict(command=cmd,exit=r.returncode,lock_before=lock,lock_after=sha(S/'Cargo.lock'),charon_sha256=sha(C),aeneas_sha256=sha(A),toolchain_env=env['RUSTUP_TOOLCHAIN'],reported_charon_toolchain='nightly-2026-06-01',llbc_sha256=sha(p) if p.exists() else None,features=features,shape=shape,root=root,source_manifest='NHA_SCRATCH_INPUTS.json')
(B/(x['attempt']+'-pins.json')).write_text(json.dumps(pins,indent=2));assert pins['lock_before']==pins['lock_after'],'STOP lock drift'
raise SystemExit(r.returncode)
