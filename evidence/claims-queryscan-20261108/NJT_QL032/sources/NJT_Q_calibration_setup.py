from pathlib import Path
import json,hashlib,lzma,base64,difflib
B=Path(__file__).resolve().parent;S=B/'NJT_Q_src';p=S/'crates/aspis-core/src/r0_transcript.rs';t=p.read_text();assert 'mod NJT_Q_array8_calibration' not in t;t+='\n'+(B/'NJT_Q_array8_calibration.rs.txt').read_text();p.write_text(t);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=B/'NJT_Q_SOURCE_PINS.json';pins=json.loads(f.read_text());pins['crates/aspis-core/src/r0_transcript.rs']=sha(p);f.write_text(json.dumps(pins))
payload=json.loads(lzma.decompress(Path('/home/dombarker/project-offloads/codex-cx-claims-queryscan-20261108/NJT_FROZEN_PAYLOAD.json.xz').read_bytes()));patch=''
for n in ['crates/aspis-core/src/lib.rs','crates/aspis-core/src/r0_transcript.rs']:
 patch+=''.join(difflib.unified_diff(base64.b64decode(payload[n]).decode().splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJT_Q_NATIVE.patch').write_text(patch);print('strict array8 fidelity calibration installed in owned cfg scratch')
