#!/usr/bin/env python3
"""Prepare/check exact production BatchedWeights source, never rewrite bodies."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, subprocess

repo=Path(__file__).resolve().parents[5]
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
out=Path(__file__).resolve().parent/'rho-input'
parser=repo/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
sha=lambda b:hashlib.sha256(b).hexdigest()
revision='925dc4b95ad6986fd76471fca857d4e2100f1cbf'
outputs={};spans=[]
def take(name,path,anchor):
    f=repo/path;raw=f.read_bytes()
    assert raw==subprocess.check_output(['git','-C',str(repo),'show',revision+':'+path])
    body,start,end,first,last=cut.find_item(f,anchor)
    outputs['fragments/'+name+'.rs']=body
    spans.append(dict(name=name,path=path,start_byte=start,end_byte_exclusive=end,
        first_line=first,end_line_exclusive=last,source_sha256=sha(raw),sha256=sha(body)))
    return body.decode()+'\n'
field='crates/aspis-core/src/field.rs';ver='crates/aspis-r1-cost-probe/src/verifier.rs'
p=take('modulus',field,'pub const P: u32')
m=take('m31',field,'pub struct M31(pub u32)')
c=take('cm31',field,'pub struct CM31 {')
k=take('qm31',field,'pub struct QM31 {')
r=take('reduce_u64',field,'fn reduce_u64(x: u64)')
rm=take('m31_reduce',field,'pub fn reduce_u64(value: u64)')
err=take('error',ver,'pub enum Error { Parse,Semantic')
carrier=take('batched_weights',ver,'struct BatchedWeights {')
impl=take('batched_weights_impl',ver,'impl BatchedWeights {')
lib=('extern crate alloc;\nextern crate self as aspis_core;\npub mod field {\n'+p+m+c+k+r+'impl M31 {\n'+rm+'}\n}\n'
    # Heap is deliberately not interpreted by this extraction. Only push/value/
    # finish are roots. New/allocation requires a separate source proof.
    'pub mod r0 { pub mod heap { use alloc::vec::Vec;\n'
    'pub fn filled<T:Copy>(_:usize,_:T)->Result<Vec<T>,()> {unreachable!()}\n}}\n'
    'pub mod verifier { use alloc::vec::Vec; use crate::field::{QM31 as K,M31};\n'+err+carrier+impl+'}\n')
outputs['lib.rs']=lib.encode()
outputs['Cargo.toml']=b'[package]\nname="aspis-r1-cu-rho"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n'
outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-cu-rho"\nversion = "0.0.0"\n'
pins=dict(revision=revision,cuts=spans,kit_files={n:sha(b) for n,b in outputs.items()},
    features=[],production_features=['pool-adapter','private-leaf-salts'],
    roots=['crate::verifier::_::push','crate::verifier::_::value'],
    opaque_paths=['crate::r0::heap::filled'],
    scope='Exact complete BatchedWeights impl and reducer/type cuts. Namespace layout only. Push/value roots; finish initially emitted but blocked on mutable-enumerate runtime interface and remains a separate required obligation. Heap stub must be opaque and is not a source proof; no allocation or whole-caller claim.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
    pth=out/n
    if a.check: assert pth.read_bytes()==b,n
    else: pth.parent.mkdir(parents=True,exist_ok=True);pth.write_bytes(b)
print(json.dumps(dict(check=a.check,revision=revision,cuts=len(spans),lib_sha256=sha(outputs['lib.rs']))))
