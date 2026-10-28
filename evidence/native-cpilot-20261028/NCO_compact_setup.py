from pathlib import Path
import subprocess,json,difflib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-cpilot-20261028';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';n='crates/aspis-r1-cost-probe/src/compact.rs'
base=subprocess.check_output(['git','show',rev+':'+n],text=True)
s=base.replace('fn compact_row(row: u8)', '#[cfg_attr(kani, kani::ensures(|r| (*r == NCO_compact::reference::compact_row_ref(row)) != cfg!(NCO_invert_compact)))]\nfn compact_row(row: u8)',1)+'\n#[cfg(kani)]\n#[path="NCO_compact.rs"]\nmod NCO_compact;\n'
s=s.replace('pub fn expand_values(compact:', '#[cfg_attr(kani, kani::requires(compact.len()==16 && out.len()==32))]\n#[cfg_attr(kani, kani::modifies(out))]\n#[cfg_attr(kani, kani::ensures(|r| (r.is_ok() && NCO_compact::expanded_one(compact,out)) != cfg!(NCO_invert_expand)))]\npub fn expand_values(compact:',1)
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});n={n!r};p=b/'NCO_src'/n
if p.is_symlink():p.unlink()
p.write_text({s!r});pins=json.loads((b/'NCO_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(b/'NCO_SOURCE_PINS.json').write_text(json.dumps(pins))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NCO_compact.patch').write_text(''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
