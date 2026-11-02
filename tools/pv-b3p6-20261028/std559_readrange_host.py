"""Isolate two std helper entry adapters without the terminal's formatter cone."""
from pathlib import Path
import sys,json,hashlib,subprocess
from run import H,run
R=H/'resume18';O=R/'std559-readrange';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
stage=sys.argv[1];assert stage in ('charon','aeneas')
ident={'charon':79180,'aeneas':79181}[stage];assert '--inside' in sys.argv or not (R/f'N{ident}').exists()
c=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon');a=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2')
assert sha(c)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(a)=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
P=H/'source/tools/pv-b3p6-20261028/std559';llbc=O/'Std559.llbc'
if stage=='charon':
 cmd=['timeout','300','taskset','--cpu-list','0-3',str(c),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default']
 for name in ['range_nth','array_read16']:cmd+=['--start-from','crate::'+name]
 names=['core::iter::range::*::nth','core::iter::range::*::spec_nth','core::iter::range::*::forward_checked','core::iter::range::*::forward_unchecked','core::array::*::index']
 for name in names:cmd+=['--include',name]
 cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--features','ct-host-prover','--release','--locked','--offline','--lib','--jobs','4']
else:
 assert not json.loads(llbc.read_text()).get('has_errors',False)
 gen=O/'generated';gen.mkdir(exist_ok=True)
 cmd=['timeout','300',str(a),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_Std559ReadRange227','-dest',str(gen),'-split-files','-emit-json',str(llbc)]
inputs=dict(stage=stage,command=cmd,charon_sha256=sha(c),aeneas_sha256=sha(a),translator_identity='functionally identical rebuild (ae1-2)',source_revision=(R/'std559-source-revision').read_text().strip(),entry_source_sha256=sha(P/'std559.rs'),manifest_sha256=sha(P/'Cargo.toml'),lock_sha256=sha(P/'Cargo.lock'),expected_time='optimized cached compilation and translation of two isolated standard helper paths; no arithmetic elimination',limitation='entry adapters are new; exact std item identity/instantiation and caller association must be checked before transfer')
(O/(stage+'-inputs.json')).write_text(json.dumps(inputs,indent=2)+'\n')
if '--inside' in sys.argv:
 if stage=='charon':
  meta=json.loads(subprocess.check_output(['cargo','+1.94.1','metadata','--manifest-path',str(P/'Cargo.toml'),'--features','ct-host-prover','--locked','--offline','--format-version','1'],text=True))
  pkgs={p['id']:p for p in meta['packages']}
  nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features'])for n in meta['resolve']['nodes']]
  expected=json.loads((H/'features227-resume4.json').read_text())['validation']['nodes']
  strip=lambda ns:sorted([n for n in ns if n['name'] not in ('pv-b3p6-reference227','aspis-r1-cost-probe')],key=lambda n:(n['name'],n['version']))
  assert strip(nodes)==strip(expected), 'dependency feature mismatch (adapter and replaced cost-probe root excluded)'  
  (O/'features.json').write_text(json.dumps(dict(nodes=nodes,mismatches=[],excluded_roots=['pv-b3p6-reference227','aspis-r1-cost-probe'],reason='entry adapters isolate std calls; core/statement/prover/dependency features exactly match'),indent=2)+'\n')
 raise SystemExit(subprocess.run(cmd).returncode)
status=run('resume18/N'+str(ident),['python3',str(Path(__file__)),stage,'--inside'],inputs['expected_time'],{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target'),'CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'false','CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS':'false'})
print(json.dumps(dict(stage=stage,id=ident,exit=status)),flush=True);raise SystemExit(status)
