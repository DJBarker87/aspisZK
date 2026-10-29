"""Extract the unchanged deployed prepared-product leaf, including its loops.
The source model will be compared with the owned unroll; no stub is supplied.
"""
from run import H, run
from pathlib import Path
import hashlib,json,sys
stage=sys.argv[1];assert stage in ['charon','aeneas']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
root=H/'source-prepared-resume12';root.mkdir(exist_ok=True)
freeze=json.loads((H/'native227-composition-source-freeze.json').read_text())
assert all(sha(H/'source'/n)==s for n,s in freeze.items())
charon=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon')
aeneas=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas')
assert sha(charon)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(aeneas)=='562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'
llbc=root/'PV_B3P_SourcePrepared12.llbc'
if stage=='charon':
 cmd=json.loads((H/'charon227-resume5-composition-r1/target.json').read_text())['command']
 cmd[cmd.index('--start-from')+1]='aspis_core::field::qm31_sum_products3_prepared'
 cmd[cmd.index('--dest-file')+1]=str(llbc)
else:
 (root/'generated').mkdir(exist_ok=True)
 cmd=['timeout','300',str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_SourcePrepared12','-dest',str(root/'generated'),'-split-files','-emit-json',str(llbc)]
(root/(stage+'-inputs.json')).write_text(json.dumps(dict(command=cmd,charon_sha256=sha(charon),aeneas_sha256=sha(aeneas),source_hashes={n:s for n,s in freeze.items() if n.endswith('.rs')},features_record='features227-resume4.json',profile='release / debug assertions off / overflow checks off',extractor_toolchain='nightly-2026-06-01'),indent=2)+'\n')
r=run('source-prepared227-resume12-'+stage,cmd,'pinned extraction of original deployed prepared-product nested loops; compilation and translation only',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')})
if r:raise SystemExit(r)
outputs=[llbc] if stage=='charon' else list((root/'generated').glob('*'))
(root/(stage+'-outputs.json')).write_text(json.dumps([dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in outputs],indent=2)+'\n')
