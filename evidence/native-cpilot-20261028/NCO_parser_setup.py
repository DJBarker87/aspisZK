from pathlib import Path
import subprocess,json,difflib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-cpilot-20261028';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';n='crates/aspis-r1-cost-probe/src/r1_wire.rs'
base=subprocess.check_output(['git','show',rev+':'+n],text=True)
s=base.replace('pub const fn row_shape', '#[cfg_attr(kani, kani::ensures(|r| (*r == NCO_wire::reference::row_shape_ref(row)) != cfg!(NCO_invert_shape)))]\npub const fn row_shape',1)
s=s.replace('pub fn parse_record(row:', '#[cfg_attr(kani, kani::requires(row<14 && record.len()<=37 && (!cfg!(NCO_header) || record.len()<=5) && (!cfg!(NCO_payload) || (row==2 && record.len()==37))))]\n#[cfg_attr(kani, kani::ensures(|r| (if cfg!(NCO_status) {r.is_ok() == NCO_wire::reference::parse_record_ref(row,record).is_ok()} else {NCO_wire::matches_ref(r,&NCO_wire::reference::parse_record_ref(row,record))}) != cfg!(NCO_invert_parse)))]\npub fn parse_record(row:',1)
s=s.replace("fn parse_record_at<'a>(", "#[cfg_attr(kani, kani::requires(row<14 && offset<=5 && bytes.len()==42))]\n#[cfg_attr(kani, kani::ensures(|r| r.is_ok() == NCO_wire::reference::parse_at_ref(bytes,row,offset).is_ok()))]\nfn parse_record_at<'a>(",1)
s=s.replace('#[derive(Clone, Copy, Debug, PartialEq, Eq)]', '#[cfg_attr(kani, derive(kani::Arbitrary))]\n#[derive(Clone, Copy, Debug, PartialEq, Eq)]',1)
s=s.replace('fn validate_record_fields(row:', '#[cfg_attr(kani, kani::requires(payload.len()==32))]\n#[cfg_attr(kani, kani::ensures(|r| (if cfg!(NCO_weak_validate) {r.is_ok() == NCO_wire::reference::validate_ref(row,payload).is_ok()} else {NCO_wire::validate_matches(r,&NCO_wire::reference::validate_ref(row,payload))}) != cfg!(NCO_invert_validate)))]\nfn validate_record_fields(row:',1)
s+='\n#[cfg(kani)]\n#[path="NCO_wire.rs"]\nmod NCO_wire;\n'
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});n={n!r};p=b/'NCO_src'/n
if p.is_symlink():p.unlink()
p.write_text({s!r});pins=json.loads((b/'NCO_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(b/'NCO_SOURCE_PINS.json').write_text(json.dumps(pins))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NCO_parser.patch').write_text(''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
assert 'pub(super) fn matches_ref' in __import__('NCO_patch').files()['crates/aspis-r1-cost-probe/src/NCO_wire.rs']
