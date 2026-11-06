from pathlib import Path
import json,lzma,hashlib,subprocess,base64
B=Path(__file__).resolve().parent;S=B/'NKJ_src'
raw=lzma.decompress((B/'NKJ_FROZEN.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(B/'NKJ_FROZEN.json.sha256').read_text().strip()
pins={}
for n,t in json.loads(raw).items():
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(t));pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
p=S/'crates/aspis-core/src/field.rs';p.write_text(p.read_text()+'\n#[cfg(kani)]\nmod NKJ_segments;\nmod NKJ_reference;\n')
(S/'crates/aspis-core/src/field/NKJ_reference.rs').write_text((B/'NKJ_reference.rs.txt').read_text())
(B/'NKJ_FROZEN_PINS.json').write_text(json.dumps(pins,indent=2))
r=subprocess.run(['patch','-p1','--forward','-i',str(B/'NKJ_KMX.patch')],cwd=S,capture_output=True,text=True)
(B/'NKJ_KMX_APPLY.log').write_text(r.stdout+r.stderr);assert r.returncode==0
print('NKJ frozen source restored, reference installed, exact KMX applied')
