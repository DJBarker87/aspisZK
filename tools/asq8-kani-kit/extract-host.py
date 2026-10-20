#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021')
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
PINS={str(T/'charon-target/release/charon'):'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',str(T/'charon-target/release/charon-driver'):'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45',str(A):'4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'}
for p,h in PINS.items():assert sha(p)==h,p
phase=sys.argv[1];cone=sys.argv[2];out=H/('extraction-'+cone+'-v1');out.mkdir(exist_ok=True)
llbc=out/'R20.llbc'
opaque=['aspis_core','aspis_statement','solana_program']
layouts=['solana_program_error::ProgramError','aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public']
if phase=='charon':
 cmd=[str(T/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--include','core::option::_::ok_or']
 roots=['crate::pair_forest::split_pair_forest_terminal_bump_hints_v1'] if cone=='strip' else ['crate::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_request_reference_v1']
 opaque=[x for x in opaque if not (cone=='encoder' and x=='aspis_statement')]
 for x in roots:cmd+=['--start-from',x]
 for x in opaque:cmd+=['--opaque',x]
 for x in layouts:cmd+=['--include',x]
 cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(H/('src/programs/aspis-pool/Cargo.toml' if cone=='strip' else 'src/crates/aspis-statement/Cargo.toml')),'--locked','--offline','--release','--lib','--no-default-features','--features',('r1-split-checkpoint,no-entrypoint' if cone=='strip' else 'pool-v1-kernel'),'--jobs','1']
else:
 raw=json.loads(llbc.read_text());assert not raw['has_errors']
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',('AspisR20Pool' if cone=='strip' else 'AspisR20Request'),'-dest',str(out/'generated'),'-subdir',('AspisR20Pool' if cone=='strip' else 'AspisR20Request'),'-split-files','-emit-json',str(llbc)]
env=dict(os.environ);env.update(RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(H/'charon-target'),CARGO_NET_OFFLINE='true',RUSTFLAGS='--cfg aeneas_ref -C link-arg=-Wl,--threads=4')
for n in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(n,None)
(out/(phase+'-input.json')).write_text(json.dumps(dict(tool_pins=PINS,command=cmd,opaque_paths=opaque,transparent_data_layouts=layouts,source_hashes={str(p.relative_to(H/'src')):sha(p) for folder in ['programs/aspis-pool/src','crates/aspis-statement/src/pool_v1'] for p in (H/'src'/folder).glob('*.rs')},source_revision=(H/'source-revision.txt').read_text().strip(),classification='Exact Pool source, unchanged; SDK and downstream boundaries opaque; no Pool or verifier source edit'),indent=2)+'\n')
raise SystemExit(subprocess.call([str(H/'harness/capped-run.sh'),'r20-'+cone+'-v1'+'-'+phase,'Compilation and pinned '+phase+' lowering only; no arithmetic execution or proof generation',str(H/'src'),'--',*cmd],env=env))
