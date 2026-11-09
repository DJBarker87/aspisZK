#!/usr/bin/env python3
"""PCWA_make_cut.py RUN_WADM RUN_S8: specs for the two cut-crate extractions.
WADM: Aeneas-only reproduction from the committed LLBC (evidence/writer-adm-20261025/WAdm_AENEAS004/sources/WAdm_Fissioned.llbc, sha256
 5d06e116... = the source_hashes entry of WAdm_AENEAS004/receipt.json); Charon is not re-run (original Charon receipt WAdm_CHARON002 used
 nightly-2026-06-01 and a fixture crate that is not committed as a crate; its two source files are embedded in the LLBC and hash-match the receipt).
S8: tools/s8-kani-20261021 crate (committed) + frozen aspis-core staged at the path the crate's dependency expects; argument shape of
 docs/.../s8-kani-20261021/extraction-complete/{charon,aeneas}-command.json; tools: XRa Charon (same sha256 as the recorded Charon) and XRa Aeneas
 (the recorded one, aeneas-b59d5188-lean432-extended-static, is not on the host)."""
import json,subprocess,hashlib,sys,os
from pathlib import Path
E=Path(__file__).resolve().parent;REPO=E.parent.parent
def git(p,rev='research'): return subprocess.check_output(['git','-C',str(REPO),'show',rev+':'+p])
sha=lambda b:hashlib.sha256(b).hexdigest()
HOST=os.environ.get('PCWA_HOST_BASE','/home/dombarker/project-offloads/codex-pc-prov-p4a-20261109')
TOOL='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin'
TOOLSHA={'charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','aeneas-b59d5188-extended':'c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'}
LIM={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'}
wa,s8=sys.argv[1:3]
# ---- WAdm
l=git('evidence/writer-adm-20261025/WAdm_AENEAS004/sources/WAdm_Fissioned.llbc')
assert sha(l)=='5d06e116f74354f6b349829e9437044bdcbd19191ef0607a1bf902ba168eda16'
d=E/'sources/WAdm_Fissioned';d.mkdir(parents=True,exist_ok=True);(d/'WAdm_Fissioned.llbc').write_bytes(l)
out=f'{HOST}/{wa}_emitted'
ae=[f'{TOOL}/aeneas-b59d5188-extended','-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-backend','lean','-namespace','WAdm_Fissioned','-dest',f'{out}/raw','-subdir','WAdm_Fissioned','-split-files','-emit-json',f'{out}/repro.llbc']
spec=dict(run=wa,label='WAdm_Fissioned',covers=['RPz7_WAdm_Fissioned_Funs (WAdm_model)'],charon_command=[f'{TOOL}/charon'],aeneas_command=ae,tool_sha256=TOOLSHA,crate_files={},
  upload={'sources/WAdm_Fissioned/WAdm_Fissioned.llbc':'sources/WAdm_Fissioned/WAdm_Fissioned.llbc'},crate_dir_rel=wa+'_crate',target_dir=wa+'_target',
  skip_charon=dict(llbc_upload='sources/WAdm_Fissioned/WAdm_Fissioned.llbc',sha256=sha(l),reason='Charon step not repeated: original WAdm_CHARON002 used nightly-2026-06-01 and an uncommitted fixture crate manifest; the committed LLBC embeds WAdm_model.rs 90226a77.. and WAdm_lib.rs 22b715f4.. which equal the WAdm_CHARON002 source_hashes. Aeneas step of WAdm_AENEAS004 is repeated from the committed LLBC.'),
  original_outputs=None,original_receipt='evidence/writer-adm-20261025/WAdm_AENEAS004/receipt.json',
  source_provenance=dict(llbc='evidence/writer-adm-20261025/WAdm_AENEAS004/sources/WAdm_Fissioned.llbc',llbc_sha256=sha(l),charon_receipt='evidence/writer-adm-20261025/WAdm_CHARON002/receipt.json',kani_receipt='evidence/writer-adm-20261025/WAdm_KANI001/receipt.json'),expected_limits=LIM)
(E/f'{wa}_spec.json').write_text(json.dumps(spec,indent=1)+'\n')
# ---- S8
T='tools/s8-kani-20261021/'
rel=['Cargo.toml','Cargo.lock','src/lib.rs','src/frozen.rs','src/owned.rs','src/proofs.rs','src/tests.rs']
dd=E/'sources/S8_tools_crate';cf={};up={}
for r in rel:
    b=git(T+r);p=dd/r;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);cf[r]=dict(upload='sources/S8_tools_crate/'+r,sha256=sha(b));up['sources/S8_tools_crate/'+r]='sources/S8_tools_crate/'+r
ws=f'{HOST}/{s8}_ws';crate=f'{ws}/tools/s8-kani-20261021';out=f'{HOST}/{s8}_emitted'
old=json.loads(git('docs/research/100bit-spend-path-20261013/evidence/s8-kani-20261021/extraction-complete/charon-command.json'))
ch=[f'{TOOL}/charon']+old[1:old.index('--dest-file')]+['--dest-file',f'{out}/repro.llbc','--','--manifest-path',f'{crate}/Cargo.toml','--offline','--release','--lib','--jobs','4']
assert old[1:3]==['cargo','--preset']
ae=[f'{TOOL}/aeneas-b59d5188-extended','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','S8OwnedP6','-dest',f'{out}/raw','-subdir','S8OwnedP6','-split-files','-emit-json',f'{out}/repro.llbc']
fz=['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-core/src/circle.rs','crates/aspis-core/src/r0/domain.rs']
froz='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
spec=dict(run=s8,label='S8OwnedP6',covers=['S8OwnedP6.Funs','S8OwnedP6.Types (check_values_owned)'],charon_command=ch,aeneas_command=ae,tool_sha256=TOOLSHA,crate_files=cf,upload=up,crate_dir_rel=f'{s8}_ws/tools/s8-kani-20261021',target_dir=s8+'_target',
  frozen_stage=dict(workspace=s8+'_ws',assert_sha256={p:sha(git(p,froz)) for p in fz},symlinks={}),
  original_outputs={'S8OwnedP6/Funs.lean':'d4d96947817065fce40dfa131fae1ec4c109df2badb3d565343230d2e59b8d87','S8OwnedP6/Types.lean':'9a745d8099951994dbcb36bbb865d300867442651d770942c49a9d0a24fd9209'},
  original_receipt='docs/research/100bit-spend-path-20261013/evidence/s8-kani-20261021/extraction-complete/artifact-pins.json',
  source_provenance=dict(crate='tools/s8-kani-20261021',note='aspis-core is the frozen 4bb3b3f tree; the S8 evidence does not pin the aspis-core revision it used'),expected_limits=LIM,
  env_extra={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true'} if False else {},
  expected_time='Cold optimized compile of the s8 crate with frozen aspis-core, then Charon and Aeneas; 180 s timeout is not raised')
(E/f'{s8}_spec.json').write_text(json.dumps(spec,indent=1)+'\n');print(wa,s8)
