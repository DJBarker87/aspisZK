#!/usr/bin/env python3
"""Exact current View.query and carriers; no parser admission is assumed."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4]
revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
parser=repo/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('source_cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
sha=lambda b:hashlib.sha256(b).hexdigest()
outputs={};spans=[]
def take(name,path,anchor):
    p=repo/path;raw=p.read_bytes()
    assert raw==subprocess.check_output(['git','-C',str(repo),'show',revision+':'+path]),path
    body,start,end,first,last=cut.find_item(p,anchor)
    outputs['fragments/'+name+'.rs']=body
    spans.append(dict(name=name,path=path,start_byte=start,end_byte_exclusive=end,
        first_line=first,end_line_exclusive=last,source_sha256=sha(raw),sha256=sha(body)))
    return body+b'\n'
field='crates/aspis-core/src/field.rs';ver='crates/aspis-r1-cost-probe/src/verifier.rs'
types=b''.join(take(name,field,anchor) for name,anchor in [
    ('m31','pub struct M31(pub u32)'),('cm31','pub struct CM31 {'),('qm31','pub struct QM31 {')])
types+=take('wide','crates/aspis-core/src/field/wide_exact.rs','pub struct WideExact {')
variant=take('variant','crates/aspis-r1-cost-probe/src/transport.rs','pub enum Variant {')
folds=take('folds','crates/aspis-r1-cost-probe/src/transport.rs','pub fn folds(self)')
constants=b''
for label,guard,name in [('initial_plain','not(feature = "private-leaf-salts")','INITIAL_QUERY_BYTES'),
    ('initial_salted','feature = "private-leaf-salts"','INITIAL_QUERY_BYTES'),
    ('second_plain','not(feature = "private-leaf-salts")','SECOND_QUERY_BYTES'),
    ('second_salted','feature = "private-leaf-salts"','SECOND_QUERY_BYTES')]:
    constants+=take(label,ver,'#[cfg('+guard+')]\npub const '+name)
view=take('view',ver,"pub struct View<'a> {")
query=take('query',ver,'pub fn query(&self,i:usize)')
outputs['lib.rs']=(b'pub mod field {\n'+types+b'}\npub mod transport {\n'+variant+
    b'impl Variant {\n'+folds+b'}\n}\npub mod verifier {\nuse crate::{field::WideExact as E,transport::Variant};\n'+
    constants+view+b"impl<'a> View<'a> {\n"+query+b'}\n}\n'+
    b"pub fn query<'a>(view:&verifier::View<'a>,index:usize)->&'a[u8] {view.query(index)}\n")
outputs['Cargo.toml']=b'[package]\nname="aspis-r1-cu-query"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[features]\nprivate-leaf-salts=[]\n[workspace]\n'
outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-cu-query"\nversion = "0.0.0"\n'
pins=dict(revision=revision,cuts=spans,kit_files={n:sha(b) for n,b in outputs.items()},
    production_features=['pool-adapter','private-leaf-salts'],
    scope='Exact View carrier, query body, folds and widths; one-call root only. No View parser, cryptographic arithmetic, or invented reduced carrier.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
    target=here/'cu-query-input'/name
    if a.check:assert target.read_bytes()==data,name
    else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
print(json.dumps(dict(check=a.check,cuts=len(spans),lib_sha256=sha(outputs['lib.rs']))))
