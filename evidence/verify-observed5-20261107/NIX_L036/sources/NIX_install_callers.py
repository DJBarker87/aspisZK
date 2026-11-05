from pathlib import Path
import json,hashlib,difflib,re
B=Path(__file__).resolve().parent;S=B/'NIX_src';pins=json.loads((B/'NIX_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NIX_FROZEN_FILE_PINS.json').read_text());patch=[]
for n,addition in [('crates/aspis-r1-cost-probe/src/sampler.rs','NIX_sampler.rs.txt'),('crates/aspis-r1-cost-probe/src/r1_wire.rs','NIX_validated.rs.txt'),('programs/r1-cost-probe/src/lib.rs','NIX_validated_program.rs.txt')]:
 p=S/n;old=p.read_text();assert 'mod NIX_' not in old;new=old+'\n'+(B/addition).read_text()
 if n.endswith('src/lib.rs'):
  new='#![cfg_attr(kani,feature(allocator_api))]\n'+new+'\n#[cfg(kani)] extern crate alloc;\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NIX_kmx;\n'
 p.write_text(new);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();frozen.pop(n,None);patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
n='crates/aspis-r1-cost-probe/src/lib.rs';p=S/n;old=p.read_text();new='#![cfg_attr(kani,feature(allocator_api))]\n'+old+'\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NIX_kmx;\n';p.write_text(new);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();frozen.pop(n,None);patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NIX_CALLERS.patch').write_text(''.join(patch));(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));(B/'NIX_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen));print('NIX sampler and actual SolanaDigest-instantiated validated dispatch installed')
