#!/usr/bin/env python3
"""PCXW_: write <run>_spec.json for PCXW_run.py extract.  usage: PCXW_mkspec.py charon|aeneas RUN INPUT_DIR_NAME [LLBC_RUN]
Shape (binding): cargo --jobs 4 AND CARGO_BUILD_JOBS=4, rustc -Zthreads=1, stable --dest-file (W/PCXW_llbc/<run>.llbc) with
<run>_emitted/repro.llbc symlinked to it, original tools first (Charon daad69be XRa_bin + Aeneas 959659a6 p4c rebuild),
Aeneas-only run on the saved LLBC.  identity by class receipt PCWE_E003."""
import json,sys,shlex
kind,run,inp=sys.argv[1:4];llbc_run=sys.argv[4] if len(sys.argv)>4 else run
tool=sys.argv[5] if len(sys.argv)>5 else 'original'
W='/home/dombarker/project-offloads/codex-pc-pin2-probe-20261111';B='/home/dombarker/project-offloads/codex-pc-prov-p9h-20261110'
P='/home/dombarker/project-offloads'
T={'original':dict(charon=P+'/codex-cx-extraction-repro1-20261027/XRa_bin/charon',aeneas=P+'/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas',tc='nightly-2026-06-01'),
   'second':dict(charon=P+'/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin/charon',aeneas=P+'/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin/aeneas',tc='nightly-2026-09-17')}[tool]
llbc=f'{W}/PCXW_llbc/{llbc_run}.llbc';emit=f'{B}/{run}_emitted'
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN=T['tc'],CARGO_BUILD_JOBS='4',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',
  CARGO_PROFILE_RELEASE_CODEGEN_UNITS='2',RUSTFLAGS='-Zthreads=1 -C overflow-checks=yes -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1',
  CARGO_TARGET_DIR=f'{W}/PCXW_target_{tool}',CARGO_NET_OFFLINE='true')
if kind=='charon':
    argv=[T['charon'],'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::extraction_probe::terminal_qm31_probe',
          '--dest-file',llbc,'--','--manifest-path',f'{W}/{inp}/Cargo.toml','--package','aspis-r1-mask-extraction-probe','--features','r0,pool-v1-kernel',
          '--no-default-features','--release','--lib','--locked','--offline','--jobs','4']
    pre=f'mkdir -p {emit} && ln -sfn {llbc} {emit}/repro.llbc && '
    collect=[run+'_emitted']
    expected='Charon on the probe crate with cold target dir: v4 recorded 73 s warm'
else:
    argv=[T['aeneas'],'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PCXW_Probe','-dest',emit+'/raw','-subdir','PCXW_Probe',
          '-split-files','-emit-json','-print-unknown-externals','-loops-to-rec',llbc]
    pre=f'mkdir -p {emit} && ln -sfn {llbc} {emit}/repro.llbc && '
    collect=[run+'_emitted']
    expected='Aeneas-only on saved LLBC; v4 recorded 9 s'
cmd=['bash','-c',pre+'exec '+' '.join(shlex.quote(x) for x in argv)]
json.dump(dict(run=run,kind=kind,tool=tool,input=inp,tools=T,command=cmd,argv=argv,env=env,collect=collect,expected=expected,
  identity_note='identity by class receipt PCWE_E003; cargo --jobs 4 and CARGO_BUILD_JOBS=4; rustc -Zthreads=1'+('' if tool=='original' else '; SECOND TOOL VERSION (Charon 454586e9 / Aeneas 0d21a9ec)'),
  spec_id=run),open(f'{run}_spec.json','w'),indent=1)
