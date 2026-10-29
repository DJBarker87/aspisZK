from run import H,run
from pathlib import Path
import json,hashlib,sys,shutil
stage,group=sys.argv[1:3];suffix=sys.argv[3] if len(sys.argv)>3 else '';assert stage in ['charon','aeneas'];assert group in ['fields','frontier','terminal','transition','rounds']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
root=H/('missing-resume14-'+group+suffix);root.mkdir(exist_ok=True)
freeze=json.loads((H/'native227-composition-source-freeze.json').read_text());assert all(sha(H/'source'/n)==s for n,s in freeze.items())
p=H/'source/tools/pv-b3p6-20261028/v244-missing14';old=p.parent/'v244';shutil.copy2(old/'Cargo.lock',p/'Cargo.lock')
c=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon');a=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas')
assert sha(c)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8';assert sha(a)=='562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'
llbc=root/'Missing14.llbc'
if stage=='charon':
 cmd=json.loads((H/'charon227-resume5-composition-r1/target.json').read_text())['command'];i=cmd.index('--start-from');cmd[i:i+2]=[]
 rootname='crate::'+group if group in ['fields','frontier'] else 'crate::reference_terminal::'+group+'_root14'
 cmd[i:i]=['--start-from',rootname,'--include','pv_b3p6_reference227::'+group]
 if group=='rounds':
  k=cmd.index('--start-from');cmd[k:k+2]=[]
  for f in ['full_round','full_round_packed','full_round_m31_constants','full_round_m31_constants_packed']:
   cmd[i:i]=['--start-from','crate::original_poseidon14::'+f]
  cmd[i:i]=['--include','pv_b3p6_reference227::original_poseidon14::*','--opaque','pv_b3p6_reference227::original_poseidon14::external_linear_lazy','--opaque','pv_b3p6_reference227::original_poseidon14::external_linear_packed']
 if group=='frontier':cmd[i:i]=['--opaque','pv_b3p6_reference227::fields']
 if group=='terminal':cmd[i:i]=['--opaque','pv_b3p6_reference227::reference_terminal::terminal_parts']
 cmd[cmd.index('--manifest-path')+1]=str(p/'Cargo.toml');cmd[cmd.index('--dest-file')+1]=str(llbc)
else:
 (root/'generated').mkdir(exist_ok=True)
 cmd=['timeout','300',str(a),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_Missing14'+group.title(),'-dest',str(root/'generated'),'-split-files','-emit-json',str(llbc)]
(root/(stage+'-inputs.json')).write_text(json.dumps(dict(command=cmd,charon_sha256=sha(c),aeneas_sha256=sha(a),source_freeze=freeze,input_hashes={str(f.relative_to(H/'source')):sha(f)for f in p.iterdir()if f.is_file()},features_record='features227-resume4.json',profile='release, debug assertions off, overflow checks off',extractor_toolchain='nightly-2026-06-01',purpose='Exact owned body tokens, relocated nested functions with same imports, or unchanged prefix plus free method root; no generated-output edits.'),indent=2)+'\n')
r=run('missing227-resume14-'+group+'-'+stage+suffix,cmd,'pinned extraction, translation/compilation only; no elimination or proof generation',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')})
if r:raise SystemExit(r)
paths=[llbc]if stage=='charon'else list((root/'generated').glob('*'))
(root/(stage+'-outputs.json')).write_text(json.dumps([dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size)for q in paths],indent=2)+'\n')
