"""Fresh pinned extraction for b3p6-1's required exact-owned-text hash chain.
Reason for replay: prior extraction receipts did not pin every input/output edge.
The private source and all frozen shipped files remain unchanged.
"""
from run import H, run
from pathlib import Path
import hashlib, json, subprocess, sys
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
stage = sys.argv[1]
assert stage in ['charon','aeneas']
root = H/'reproduce-resume12'
root.mkdir(exist_ok=True)
freeze = json.loads((H/'native227-composition-source-freeze.json').read_text())
assert all(sha(H/'source'/n)==s for n,s in freeze.items())
inputs = {str(p.relative_to(H/'source')):sha(p) for p in (H/'source/tools/pv-b3p6-20261028/v244').glob('*') if p.is_file()}
charon = Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon')
aeneas = Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas')
assert sha(charon)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(aeneas)=='562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'
llbc = root/'PV_B3P_227_composition_resume5.llbc'
old = H/'PV_B3P_227_composition_resume5.llbc'
if stage=='charon':
    cmd = json.loads((H/'charon227-resume5-composition-r1/target.json').read_text())['command']
    cmd[cmd.index('--dest-file')+1] = str(llbc)
else:
    cmd = json.loads((H/'aeneas227-resume5-composition/target.json').read_text())['command']
    cmd[cmd.index('-dest')+1] = str(root/'generated')
    cmd[-1] = str(llbc)
    (root/'generated').mkdir(exist_ok=True)
snapshot = dict(stage=stage,inputs=inputs,source_freeze_sha256=sha(H/'native227-composition-source-freeze.json'),charon_sha256=sha(charon),aeneas_sha256=sha(aeneas),features=json.loads((H/'features227-resume4.json').read_text()),command=cmd)
(root/(stage+'-inputs.json')).write_text(json.dumps(snapshot,indent=2)+'\n')
r = run('reproduce227-resume12-'+stage,cmd,'pinned extraction reproduction and exact hash-chain evidence; no arithmetic elimination',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')})
if r: raise SystemExit(r)
assert inputs=={str(p.relative_to(H/'source')):sha(p) for p in (H/'source/tools/pv-b3p6-20261028/v244').glob('*') if p.is_file()}
outputs = [llbc] if stage=='charon' else list((root/'generated').glob('*'))
checks = []
for p in outputs:
    q = old if stage=='charon' else H/'generated227-resume5-composition'/p.name
    checks.append(dict(path=str(p),sha256=sha(p),old_path=str(q),old_sha256=sha(q) if q.exists() else None,byte_identical=q.exists() and p.read_bytes()==q.read_bytes()))
(root/(stage+'-outputs.json')).write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks))
