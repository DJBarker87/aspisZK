from pathlib import Path
import json,hashlib,lzma,base64,difflib
B=Path(__file__).resolve().parent;S=B/'NKQ_src';pins=json.loads((B/'NKQ_SOURCE_PINS.json').read_text());payload=json.loads(lzma.decompress((B/'NKQ_FROZEN_PAYLOAD.json.xz').read_bytes()))
n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=S/n
assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n]
p.write_bytes(base64.b64decode(payload[n])+b'\n#[cfg(kani)]\n#[path="NKQ_rejections.rs"]\npub(crate) mod NKQ_rejections;\n')
q=p.with_name('NKQ_rejections.rs');assert hashlib.sha256(q.read_bytes()).hexdigest()==pins[str(q.relative_to(S))];q.write_text((B/'NKQ_rejections.rs.txt').read_text())
w=p.with_name('NKQ_windows.rs');w.write_text((B/'NKQ_windows.rs.txt').read_text())
p.write_text(p.read_text()+'\n#[cfg(kani)]\n#[path="NKQ_windows.rs"]\npub(crate) mod NKQ_windows;\n')
c=S/'crates/aspis-r1-cost-probe/src/candidate.rs'
c.write_bytes(base64.b64decode(payload[str(c.relative_to(S))])+b'\n#[cfg(kani)]\n#[path="NKQ_tx1.rs"]\nmod NKQ_tx1;\n')
t=c.with_name('NKQ_tx1.rs');t.write_text((B/'NKQ_tx1.rs.txt').read_text())
frozen=json.loads((B/'NKQ_FROZEN_FILE_PINS.json').read_text());frozen.pop(str(c.relative_to(S)),None);(B/'NKQ_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2))
rw=S/'crates/aspis-r1-cost-probe/src/r1_wire.rs'
rw.write_bytes(base64.b64decode(payload[str(rw.relative_to(S))])+b"\n#[cfg(kani)] pub(crate) fn NKQ_prefix(root: &[u8;32])->Prefix<'_>{Prefix{c1_root:root,records:[&root[..0];27]}}\n#[cfg(kani)] pub(crate) fn NKQ_transcript<H:Digest32>(state:[u8;32],hash:H,next_row:u8)->SemanticTranscript<H>{SemanticTranscript{state,hash,next_row}}\n")
frozen.pop(str(rw.relative_to(S)),None);(B/'NKQ_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2))
for f in [p,q,w,c,t,rw]:pins[str(f.relative_to(S))]=hashlib.sha256(f.read_bytes()).hexdigest()
(B/'NKQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
patch=''
for n in pins:
 if n.startswith('KMX'):continue
 old=base64.b64decode(payload[n]).decode() if n in payload else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n if n in payload else '/dev/null',tofile='b/'+n))
(B/'NKQ_NATIVE.patch').write_text(patch);print('Own cfg-only module path/harness repaired; frozen bodies retained')
