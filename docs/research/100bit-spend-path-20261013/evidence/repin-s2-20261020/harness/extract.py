#!/usr/bin/env python3
"""Extract frozen S2 owners; no Rust source rewriting or surrogate crate."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-repin-s2-20261020')
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
PINS={str(T/'charon-target/release/charon'):'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',str(T/'charon-target/release/charon-driver'):'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45',str(A):'4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items(): assert sha(p)==h,p
phase,cone=sys.argv[1:]
out=H/('extraction-'+cone);out.mkdir(exist_ok=True)
llbc=out/'S2.llbc'
# Downstream verifier/decoder and SDK calls are explicit extraction boundaries.
opaque=['aspis_core','aspis_statement','aspis_r1_cost_probe','solana_program','crate::r1_pool_adapter']
roots=['crate::observer','crate::first','crate::first_decoded'] if cone=='first' else ['crate::observer','crate::r1_pool_adapter::stage1','crate::r1_pool_adapter::stage2','crate::process_r1_cost_probe_instruction']
layouts=['aspis_r1_cost_probe::verifier::Phase','aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public']
if phase=='charon':
 cmd=[str(T/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err']
 for x in opaque:cmd+=['--opaque',x]
 for x in layouts:cmd+=['--include',x]
 for x in roots:cmd+=['--start-from',x,'--include',x]
 cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(H/'src/programs/r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--features','pool-adapter,private-leaf-salts','--jobs','1']
else:
 raw=json.loads(llbc.read_text());assert not raw['has_errors']
 cmd=[str(A),'-log-debug','Translate,InterpLoops','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1S2'+cone.title(),'-dest',str(out/'generated'),'-subdir','AspisR1S2'+cone.title(),'-split-files','-emit-json',str(llbc)]
env=dict(os.environ);env.update(RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(H/'charon-target'),RUSTFLAGS='-C link-arg=-Wl,--threads=4')
for n in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(n,None)
(out/(phase+'-input.json')).write_text(json.dumps(dict(tool_pins=PINS,command=cmd,opaque_paths=opaque,transparent_data_layouts=layouts,roots=roots,source_hashes={str(p.relative_to(H/'src')):sha(p) for d in ['programs/r1-cost-probe/src','crates/aspis-r1-cost-probe/src'] for p in (H/'src'/d).glob('*.rs')},source_revision=(H/'source-revision.txt').read_text().strip(),cu_profiling=False),indent=2)+'\n')
raise SystemExit(subprocess.call([str(H/'harness/capped-run.sh'),'extract-'+cone+'-'+phase,'Compilation and pinned '+phase+' lowering; no arithmetic gate',str(H/'src'),'--',*cmd],env=env))
