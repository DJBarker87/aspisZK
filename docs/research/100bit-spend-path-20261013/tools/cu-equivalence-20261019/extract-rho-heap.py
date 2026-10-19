#!/usr/bin/env python3
"""Exact generic heap::filled body with one declaration-owner rename."""
from pathlib import Path
import argparse,hashlib,importlib.util,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
parser=repo/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
source=repo/'crates/aspis-core/src/r0/heap.rs';body,*_=cut.find_item(source,'pub fn filled<T: Copy>(')
error,*_=cut.find_item(repo/'crates/aspis-core/src/r0/mod.rs','pub enum Error {')
renamed=body.replace(b'pub fn filled<T: Copy>(',b'pub fn source_filled<T: Copy>(',1)
assert renamed.replace(b'pub fn source_filled<T: Copy>(',b'pub fn filled<T: Copy>(',1)==body
lib=b'extern crate alloc;\npub mod r0 {\n'+error+b'\npub mod heap {use super::Error;use alloc::vec::Vec;\n'+renamed+b'\n}\n}\n'
outputs={'lib.rs':lib,'fragments/filled.rs':body,'fragments/error.rs':error,
    'Cargo.toml':b'[package]\nname="aspis-r1-rho-heap"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n',
    'Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-rho-heap"\nversion = "0.0.0"\n'}
pins=dict(production_revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9',source=str(source.relative_to(repo)),
    source_sha256=sha(source.read_bytes()),filled_sha256=sha(body),features=[],
    roots=['crate::r0::heap::source_filled'],opaque_paths=['alloc::vec::_::try_reserve_exact'],
    kit_files={n:sha(b) for n,b in outputs.items()},
    scope='Whole generic filled body, source_filled declaration rename only. Standard reserve is an explicit boundary; its success is not assumed by the helper length theorem. The unchanged original runtime resize is used.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
    p=here/'rho-heap-input'/name
    if args.check:assert p.read_bytes()==data,name
    else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=args.check,lib_sha256=sha(lib),body_unchanged=True)))
