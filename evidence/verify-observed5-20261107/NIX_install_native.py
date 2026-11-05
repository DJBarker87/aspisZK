from pathlib import Path
import json,subprocess,hashlib
B=Path(__file__).resolve().parent;S=B/'NIX_src'
manifest=json.loads((B/'NHR_STAGING_MANIFEST.json').read_text())
pins={n:v['sha256'] for n,v in manifest['files'].items()}
r=subprocess.run(['git','apply',str(B/'NIX_KMX.patch')],cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
n='crates/aspis-core/src/r0/heap.rs';p=S/n;p.write_text(p.read_text()+'\n'+(B/'NIX_heap.rs.txt').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
n='crates/aspis-core/src/lib.rs';p=S/n;p.write_text(p.read_text()+'\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NIX_kmx;\n');pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NIX_FROZEN_FILE_PINS.json').write_text(json.dumps({n:h for n,h in pins.items() if n not in ['crates/aspis-core/src/r0/heap.rs','crates/aspis-core/src/lib.rs']}))
(B/'NIX_SOURCE_PINS.json').write_text(json.dumps({n:pins[n] for n in ['crates/aspis-core/src/r0/heap.rs','crates/aspis-core/src/lib.rs']}))
print('NIX heap harness installed; frozen source outside scratch unchanged')
