#!/usr/bin/env python3
"""Exact common basis prefix, with its stable accumulator-length read explicit."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
old=(here/'rho-accumulate-input/fragments/old-accumulate.rs').read_bytes()
new=(here/'rho-accumulate-input/fragments/new-accumulate.rs').read_bytes()
begin=b'    let mut basis=[M31::ZERO;256];';end=b'    for j in 0..a.weights.len() {'
prefix=old[old.index(begin):old.index(end)]
assert prefix==new[new.index(begin):new.index(end)]
read=b'a.weights.len()';assert prefix.count(read)==1
factored=prefix.replace(read,b'length');assert factored.replace(b'length',read)==prefix
field=repo/'crates/aspis-core/src/field.rs'
parser=repo/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
outputs={'fragments/common-prefix.rs':prefix}
for name,anchor in [('m31','pub struct M31(pub u32)'),('double','pub fn double(self) -> M31 {')]:
    body,*_=cut.find_item(field,anchor);outputs['fragments/'+name+'.rs']=body
lib=b'pub mod field {\n'+outputs['fragments/m31.rs']+b'''\nimpl M31 {
pub const ZERO:Self=Self(0);pub const ONE:Self=Self(1);
pub fn mul(self,_rhs:Self)->Self{unreachable!()}
pub fn add(self,_rhs:Self)->Self{unreachable!()}
pub fn sub(self,_rhs:Self)->Self{unreachable!()}
'''+outputs['fragments/double.rs']+b'\n}\n}\nuse field::M31;\npub fn basis(length:usize,mut node:M31)->[M31;256] {\n'+factored+b'    basis\n}\n'
outputs['lib.rs']=lib
outputs['Cargo.toml']=b'[package]\nname="aspis-r1-rho-basis"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n'
outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-rho-basis"\nversion = "0.0.0"\n'
pins=dict(candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611',features=[],
    common_prefix_sha256=sha(prefix),production_field_sha256=sha(field.read_bytes()),
    kit_files={n:sha(b) for n,b in outputs.items()},
    opaque_paths=['crate::field::_::mul','crate::field::_::add','crate::field::_::sub'],roots=['crate::basis'],
    scope='Exact unchanged basis statements on both candidate sides. The stable read a.weights.len() is one explicit scalar input; inverse substitution is checked. Source caller binding of this stable projection remains explicit, not an assumed equivalence of the full accumulator.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
    p=here/'rho-basis-input'/name
    if args.check:assert p.read_bytes()==data,name
    else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=args.check,lib_sha256=sha(lib))))
