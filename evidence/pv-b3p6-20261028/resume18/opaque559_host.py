"""Expand the opaque frontier at unchanged deployed bodies, then try ae1-2.
Each stage is one capped extraction scope. No source rewrite or new tool trust.
"""
from pathlib import Path
import sys,json,hashlib,subprocess
from run import H,run
R=H/'resume18';O=R/'opaque559';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
stage=sys.argv[1];assert stage in ('charon','aeneas')
ident={'charon':79168,'aeneas':79169}[stage]
assert not (R/f'N{ident}').exists(),'never reuse an extraction ID'
assert len(list(R.glob('N*/receipt/receipt.json')))<30
c=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon')
a=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2')
assert sha(c)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(a)=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
I=json.loads((R/'opaque559-upstream-command.json').read_text())
manifest=H/'source/tools/pv-b3p6-20261028/v244-direct17-terminal/Cargo.toml'
llbc=O/'Opaque559.llbc'
if stage=='charon':
 cmd=I['command'][:I['command'].index('--dest-file')]
 # Include every one of the eleven names, covering all sixteen specializations.
 names=['core::option::expect_failed','core::hint::assert_unchecked::precondition_check','core::num::*::unchecked_add::precondition_check','core::panicking::panic_nounwind_fmt','core::slice::index::*::get_unchecked::precondition_check','core::slice::index::*::get_unchecked_mut::precondition_check','core::array::drain::*::call_mut','core::iter::range::*::spec_nth','core::array::*::index','core::array::*::index_mut','core::slice::*::copy_from_slice']
 # Wrapper's lib path is the actual crate lib.rs; the crate name changes only.
 cmd=[s.replace('aspis_r1_cost_probe::','pv_b3p6_reference227::') for s in cmd]
 for n in names:cmd+=['--include',n]
 cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(manifest),'--features','ct-host-prover','--release','--locked','--offline','--lib','--jobs','4']
 pins=json.loads((H/'resume17/deployed-source-pins.json').read_text())
 for p,h in pins.items():assert sha(H/'source'/p)==h,(p,h)
 inputs=dict(stage=stage,command=cmd,added_includes=names,source_pins=pins,source_revision=(H/'revision').read_text().strip(),charon_sha256=sha(c),aeneas_sha256=sha(a),translator_identity='functionally identical rebuild (ae1-2)',upstream_command_sha256=sha(R/'opaque559-upstream-command.json'),feature_authority='features227-resume4.json and deployed direct17-terminal wrapper; optimized-terminal excluded',expected_time='optimized cached crate compilation and MIR lowering; no arithmetic elimination')
else:
 assert llbc.is_file();assert not json.loads(llbc.read_text()).get('has_errors',False)
 gen=O/'generated';gen.mkdir(exist_ok=True)
 cmd=['timeout','300',str(a),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_Opaque559227','-dest',str(gen),'-split-files','-emit-json',str(llbc)]
 inputs=dict(stage=stage,command=cmd,llbc_sha256=sha(llbc),aeneas_sha256=sha(a),translator_identity='functionally identical rebuild (ae1-2)',expected_time='translation of expanded std helper frontier; no arithmetic elimination')
(O/(stage+'-inputs.json')).write_text(json.dumps(inputs,indent=2)+'\n')
status=run('resume18/N'+str(ident),cmd,inputs['expected_time'],{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target'),'CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'false','CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS':'false'})
print(json.dumps(dict(stage=stage,id=ident,exit=status,llbc_exists=llbc.exists())),flush=True)
raise SystemExit(status)
