"""Extract exact unchanged owned wrapper spans with explicit callee boundaries.
Changing the start cone isolates previously absent declarations, not a retry of
any rejected full extraction. No generated output is edited.
"""
from run import H,run
from pathlib import Path
import json,hashlib,sys
stage,group=sys.argv[1:];assert stage in ['charon','aeneas'];assert group in ['public','terminal','semantic','bytes','publicbytes','equality','safe-equality','semantic-root13','semantic-value-root13']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
root=H/('missing-resume13-'+group);root.mkdir(exist_ok=True)
freeze=json.loads((H/'native227-composition-source-freeze.json').read_text());assert all(sha(H/'source'/n)==s for n,s in freeze.items())
c=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon');a=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas')
assert sha(c)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8';assert sha(a)=='562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'
llbc=root/'Missing13.llbc'
if stage=='charon':
 cmd=json.loads((H/'charon227-resume5-composition-r1/target.json').read_text())['command'];i=cmd.index('--start-from');cmd[i:i+2]=[]
 roots=['crate::reference_terminal::r0::Public::terminal_qm31','crate::reference_terminal::r0::Public::transition'] if group in ['public','terminal'] else ['crate::reference_terminal::r0::Public::public_bytes::fields','crate::reference_terminal::r0::Public::public_bytes::frontier']
 if group=='terminal':roots=roots[:1]
 if group=='semantic-root13':roots=['crate::reference_terminal::semantic_root13','crate::reference_terminal::transition_root13']
 if group=='semantic-value-root13':roots=['crate::reference_terminal::semantic_root13']
 if group=='safe-equality':roots=['crate::equality_value13']
 if group=='equality':roots=['crate::host_terminal::equality_value']
 if group=='publicbytes':roots=['crate::reference_terminal::r0::Public::public_bytes']
 if group=='semantic':roots=['crate::reference_terminal::private_public','crate::reference_terminal::withdrawal_public','crate::reference_terminal::r0::Public::semantic']
 args=[]
 for x in roots:args+=['--start-from',x]
 if group=='equality':args+=['--include','pv_b3p6_reference227::host_terminal::*','--include','pv_b3p6_reference227::host_terminal_field::*']
 if group=='safe-equality':
  cmd[cmd.index('--manifest-path')+1]=str(H/'source/tools/pv-b3p6-20261028/v244-safe13/Cargo.toml')
 if group in ['semantic-root13','semantic-value-root13']:
  cmd[cmd.index('--manifest-path')+1]=str(H/'source/tools/pv-b3p6-20261028/v244-d18813/Cargo.toml')
 if group in ['public','terminal']:args+=['--opaque','pv_b3p6_reference227::reference_terminal::terminal_parts']
 cmd[i:i]=args;cmd[cmd.index('--dest-file')+1]=str(llbc)
else:
 (root/'generated').mkdir(exist_ok=True)
 cmd=['timeout','300',str(a),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_Missing13'+group.title(),'-dest',str(root/'generated'),'-split-files','-emit-json',str(llbc)]
if group in ['semantic-root13','semantic-value-root13']:
 owned=H/'source/tools/pv-b3p6-20261028/v244/reference_terminal.rs';copy=H/'source/tools/pv-b3p6-20261028/v244-d18813/reference_terminal.rs';assert copy.read_bytes().startswith(owned.read_bytes())
 (root/'fresh-root-inputs.json').write_text(json.dumps(dict(unchanged_owned_prefix_sha256=sha(owned),owned_prefix_bytes=owned.stat().st_size,input_hashes={str(f):sha(f)for f in copy.parent.iterdir()if f.is_file()}),indent=2)+'\n')
(root/(stage+'-inputs.json')).write_text(json.dumps(dict(command=cmd,charon_sha256=sha(c),aeneas_sha256=sha(a),source_freeze=freeze,features_record='features227-resume4.json',features=json.loads((H/'features227-resume4.json').read_text()),profile='release, debug assertions off, overflow checks off',extractor_toolchain='nightly-2026-06-01',purpose='exact owned spans; terminal_parts callee explicitly opaque for later named Link'),indent=2)+'\n')
r=run('missing227-resume13-'+group+'-'+stage,cmd,'isolated pinned extraction of missing wrapper declarations; translation and compilation, no proof generation or elimination',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')})
if r:raise SystemExit(r)
paths=[llbc]if stage=='charon'else list((root/'generated').glob('*'))
(root/(stage+'-outputs.json')).write_text(json.dumps([dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)for p in paths],indent=2)+'\n')
print(json.dumps(dict(group=group,stage=stage,exit=r)))
