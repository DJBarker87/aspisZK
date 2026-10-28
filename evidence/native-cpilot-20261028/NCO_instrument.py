from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-cpilot-20261028';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
n='crates/aspis-r1-cost-probe/src/r1_wire.rs'
s=subprocess.check_output(['git','show',rev+':'+n],text=True)
s=s.replace('pub const fn row_shape', '#[cfg_attr(kani, kani::ensures(|r| (*r == NCO_wire::reference::row_shape_ref(row)) != cfg!(NCO_invert_shape)))]\npub const fn row_shape',1)
s+='\n#[cfg(kani)]\nmod NCO_wire;\n'
# Child reference visible to its parent only inside cfg(kani).
p=E/'NCO_wire.rs';p.write_text(p.read_text().replace('mod reference;','pub(super) mod reference;'))
files={n:s}
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r});pins=json.loads((b/'NCO_SOURCE_PINS.json').read_text())
for n,s in files.items():
 p=b/'NCO_src'/n
 if p.is_symlink():p.unlink()
 p.write_text(s);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NCO_SOURCE_PINS.json').write_text(json.dumps(pins))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
# Full scratch-only diff; no modifications to repository shipped files.
base=subprocess.check_output(['git','show',rev+':'+n],text=True)
import difflib
patch=''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NCO_instrument.patch').write_text(patch)
