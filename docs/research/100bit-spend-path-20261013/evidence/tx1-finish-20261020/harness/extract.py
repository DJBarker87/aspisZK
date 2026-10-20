#!/usr/bin/env python3
"""Pinned pipeline rooted at the frozen checkpoint serializer; no source modifications."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-tx1-finish-20261020')
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
PINS={str(T/'charon-target/release/charon'):'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',str(T/'charon-target/release/charon-driver'):'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45',str(A):'4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():assert sha(p)==h,p
phase=sys.argv[1]; attempt=sys.argv[2]; out=H/('extraction-'+attempt);out.mkdir(exist_ok=True)
llbc=out/'Tx1Finish.llbc'
layouts=['aspis_core::r0::domain::Point','aspis_core::circle::SecureCirclePoint','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact']
opaque=['aspis_core','aspis_statement','crate::weights','crate::fast_domain','crate::fast_dots','crate::fast_pairing','crate::trace']
if phase=='charon':
 cmd=[str(T/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--start-from','crate::verifier::checkpoint']
 for x in opaque:cmd+=['--opaque',x]
 # Preserve data layouts used by orchestration; their methods stay opaque.
 for x in layouts:cmd+=['--include',x]
 cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(H/'src/crates/aspis-r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--no-default-features','--features','private-leaf-salts','--jobs','1']
else:
 raw=json.loads(llbc.read_text());assert not raw['has_errors']
 cmd=[str(A),'-log-debug','Translate,InterpLoops','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1Tx1Finish','-dest',str(out/'generated'),'-subdir','AspisR1Tx1Finish','-split-files','-emit-json',str(llbc)]
env=dict(os.environ);env.update(RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(H/'charon-target'),RUSTFLAGS='-C link-arg=-Wl,--threads=4')
for n in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(n,None)
(out/(phase+'-input.json')).write_text(json.dumps(dict(tool_pins=PINS,command=cmd,opaque_paths=opaque,transparent_data_layouts=layouts,source_hashes={str(p.relative_to(H/'src')):sha(p) for p in (H/'src/crates/aspis-r1-cost-probe/src').glob('*.rs')},source_revision=(H/'source-revision.txt').read_text().strip(),classification='UNCHANGED FROZEN SOURCE; actual checkpoint serializer'),indent=2)+'\n')
raise SystemExit(subprocess.call([str(H/'harness/capped-run.sh'),'extract-'+attempt+'-'+phase,'Compilation and pinned '+phase+' lowering; no arithmetic execution or proof generation',str(H/'src'),'--',*cmd],env=env))
