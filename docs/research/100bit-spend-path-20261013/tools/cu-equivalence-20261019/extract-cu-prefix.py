#!/usr/bin/env python3
"""Pin the exact production fixed-prefix statement in a shared-reference root."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4]
source='crates/aspis-r1-cost-probe/src/fast_dots.rs'
revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
raw=(repo/source).read_bytes()
assert raw==subprocess.check_output(['git','-C',str(repo),'show',revision+':'+source])
statement=b'let q:&[u8;608]=q[..608].try_into().unwrap();'
assert raw.count(statement)==1
start=raw.index(statement);sha=lambda b:hashlib.sha256(b).hexdigest()
outputs={
 'lib.rs':b'pub fn fixed_prefix(q:&[u8])->&[u8;608] {\n    '+statement+b'\n    q\n}\n',
 'Cargo.toml':b'[package]\nname="aspis-r1-cu-prefix"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n',
 'Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-cu-prefix"\nversion = "0.0.0"\n',
}
pins=dict(revision=revision,path=source,source_sha256=sha(raw),start_byte=start,
 end_byte_exclusive=start+len(statement),statement_sha256=sha(statement),
 kit_files={n:sha(b) for n,b in outputs.items()},
 scope='Exact prefix statement, plus a free-function boundary returning that same reference. Four-dot accesses and View.query caller bounds need consuming proofs.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
    target=here/'cu-prefix-input'/name
    if a.check:assert target.read_bytes()==data,name
    else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
print(json.dumps(dict(check=a.check,statement_sha256=sha(statement),files=len(outputs))))
