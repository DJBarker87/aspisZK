#!/usr/bin/env python3
"""Factor only the exact proved zip loop so the surrounding new body can emit."""
from pathlib import Path
import argparse,hashlib,importlib.util,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
base=here/'rho-input';pins=json.loads((base/'source-pins.json').read_text());raw=(base/'lib.rs').read_bytes()
assert sha(raw)==pins['kit_files']['lib.rs']
parser=repo/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
original,*_=cut.find_item(base/'lib.rs','fn new(weights:&[K])->Result<Self,Error> {')
loop=b'''        for (out,w) in raw.iter_mut().zip(weights) {
            *out=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
        }'''
assert original.count(loop)==1
call=b'        initialize_weights(&mut raw,weights);'
factored=original.replace(loop,call);assert factored.replace(call,loop)==original
helper=b'fn initialize_weights(raw:&mut Vec<[u64;4]>,weights:&[K]) {\n'+loop+b'\n}\n'
raw=raw.replace(original,factored)
anchor=b'impl BatchedWeights {';assert raw.count(anchor)==1;raw=raw.replace(anchor,helper+anchor)
core_error,*_=cut.find_item(repo/'crates/aspis-core/src/r0/mod.rs','pub enum Error {')
stub=b'''pub mod r0 { pub mod heap { use alloc::vec::Vec;
pub fn filled<T:Copy>(_:usize,_:T)->Result<Vec<T>,()> {unreachable!()}
}}'''
assert raw.count(stub)==1
raw=raw.replace(stub,b'pub mod r0 {\n'+core_error+b'\npub mod heap { use alloc::vec::Vec;\npub fn filled<T:Copy>(_:usize,_:T)->Result<Vec<T>,super::Error>{unreachable!()}\n}}')
outputs={'lib.rs':raw,'fragments/original-new.rs':original,'fragments/factored-new.rs':factored,
         'fragments/assignment-loop.rs':loop,'fragments/initialize-helper.rs':helper,
         'fragments/core-error.rs':core_error}
for name in ['Cargo.toml','Cargo.lock']:outputs[name]=(base/name).read_bytes()
meta=dict(base_kit_sha256=pins['kit_files']['lib.rs'],production_revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9',
    candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611',features=[],
    roots=['crate::verifier::_::new'],opaque_paths=['crate::r0::heap::filled','crate::verifier::initialize_weights'],
    kit_files={n:sha(b) for n,b in outputs.items()},
    source_refinement='Lift only the exact zip assignment block to a helper with its two free borrows. Inverse inlining reproduces the complete original new body. The helper is interpreted by the proved original-runtime Zip/loan traversal and extracted assignment, not by an unproved whole-new equivalence premise.',
    scope='Complete surrounding new wrapper emission after this local loop factoring; heap remains an explicit source boundary. Original whole-new emission failures remain not admitted. Source-to-component refinement and allocation contract are still completion requirements.')
outputs['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode()
for name,data in outputs.items():
    p=here/'rho-init-wrapper-input'/name
    if args.check:assert p.read_bytes()==data,name
    else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=args.check,inverse_inlining_byte_identical=True,lib_sha256=sha(raw))))
