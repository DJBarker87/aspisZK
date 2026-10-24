#!/usr/bin/env python3
"""Focused unchanged frozen Y1 helper, full byte/status Rust gate."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);O.mkdir(exist_ok=False)
rev='b2727acd3abf79315d18b754a260f58f4b1c6326';rel='crates/aspis-r1-cost-probe/src/compact.rs'
raw=subprocess.check_output(['git','-C',str(R),'show',rev+':'+rel]).decode()
sha=lambda b:hashlib.sha256(b).hexdigest()
def block(anchor):
 a=raw.index(anchor);b=raw.index('{',a);d=1;e=b+1
 while d:d+=(raw[e]=='{')-(raw[e]=='}');e+=1
 return raw[a:e]
function=block('pub fn expand_values(');enum=block('pub enum CodecError')
assert sha(raw.encode())=='adcd99bdedda8ecdb250fb810ad9bcd263ce80a2c6cb6e7d2d3777587dabb9b7'
source='#![no_std]\n\n#[derive(Clone, Copy, Debug, PartialEq, Eq)]\n'+enum+'\n\n#[inline(always)]\n'+function+'\n\n#[cfg(kani)]\nmod proofs;\n'
(O/'src').mkdir();(O/'src/lib.rs').write_text(source)
(O/'src/proofs.rs').write_bytes(Path(__file__).with_name('proofs.rs').read_bytes())
(O/'Cargo.toml').write_text('''[package]
name = "aspis-s1-y1-source-20261024"
version = "0.1.0"
edition = "2021"
[lib]
path = "src/lib.rs"
[profile.release]
opt-level = 3
overflow-checks = true
[workspace]
''')
(O/'source-binding.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','revision':rev,'file':rel,'file_sha256':sha(raw.encode()),'function':function,'function_sha256':sha(function.encode()),'error_enum':enum,'error_enum_sha256':sha(enum.encode()),'files':{str(p.relative_to(O)):sha(p.read_bytes()) for p in O.rglob('*') if p.is_file()},'scope':'Exact unchanged frozen function and full native CodecError carrier. No refactor or stubs. Fixed Y1 positive case and bounded malformed-length case only, not a universal native/SDK/caller instance.'},indent=2)+'\n')
