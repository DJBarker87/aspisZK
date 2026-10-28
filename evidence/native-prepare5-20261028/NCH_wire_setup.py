from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-prepare5-20261028'
helper='''use super::*;
pub(crate) fn prefix<'a>(root:&'a[u8;32],records:[&'a[u8];27])->Prefix<'a>{Prefix{c1_root:root,records}}
pub(crate) fn transcript<H:Digest32>(hash:H,state:[u8;32],next_row:u8)->SemanticTranscript<H>{SemanticTranscript{state,hash,next_row}}
pub(crate) fn update<H:Digest32>(t:&mut SemanticTranscript<H>,state:[u8;32],next_row:u8){t.state=state;t.next_row=next_row;}
pub(crate) fn into_hash<H:Digest32>(t:SemanticTranscript<H>)->H{t.hash}
'''
parent=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],text=True)+'\n#[cfg(kani)]\n#[path="NCH_wire.rs"]\npub(crate) mod NCH_wire;\n'
x=dict(B=B,parent=parent,helper=helper,pins=json.loads((E/'NCH_SOURCE.json').read_text()))
code='''from pathlib import Path
import json,subprocess,hashlib
x=json.loads(PAYLOAD);b=Path(x['B']);s=b/'NCH_src'
with (b/'NCH_WIRE-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NCH_WIRE-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NCH_WIRE-reservation.json').read_text());assert r.returncode==0 and a['allowed'] is True,(r.returncode,a)
for n,content in [('r1_wire.rs',x['parent']),('NCH_wire.rs',x['helper'])]:
 p=s/'crates/aspis-r1-cost-probe/src'/n;assert not p.is_symlink();p.write_text(content)
 x['pins']['source_sha256'][str(p.relative_to(s))]=hashlib.sha256(p.read_bytes()).hexdigest()
print(json.dumps(dict(source=x['pins'],reservation=a)))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NCH_WIRE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
v=json.loads(r.stdout);(E/'NCH_SOURCE.json').write_text(json.dumps(v['source'],indent=2)+'\n')
import difflib
original=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],text=True)
patch=''.join(difflib.unified_diff(original.splitlines(True),parent.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/r1_wire.rs',tofile='b/crates/aspis-r1-cost-probe/src/r1_wire.rs'))+''.join(difflib.unified_diff([],helper.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCH_wire.rs'))
(E/'NCH_WIRE.patch').write_text(patch);print('Own scratch-only typed constructor helper installed; no shipped source mutation')
