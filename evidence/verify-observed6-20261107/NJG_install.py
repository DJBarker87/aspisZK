from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NJG_src';m=json.loads((B/'NHR_STAGING_MANIFEST.json').read_text());pins={};patch=[]
for n,addition in [('crates/aspis-core/src/r0/heap.rs',(B/'NJG_heap.rs.txt').read_text()),('crates/aspis-core/src/lib.rs','#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NJG_kmx;')]:
 p=S/n;old=p.read_text();new=old+'\n'+addition;p.write_text(new);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJG_NATIVE.patch').write_text(''.join(patch));(B/'NJG_SOURCE_PINS.json').write_text(json.dumps(pins));(B/'NJG_FROZEN_FILE_PINS.json').write_text(json.dumps({n:v['sha256'] for n,v in m['files'].items() if n not in pins}));print('NJG one-iteration window installed')
