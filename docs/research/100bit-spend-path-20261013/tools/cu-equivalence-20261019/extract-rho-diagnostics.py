#!/usr/bin/env python3
"""Exact non-prover diagnostic constructors and trace value dependency slice."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
parser=repo/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
outputs={};sources={}
def extract(name,path,anchor,scope=None):
 p=repo/path;raw=p.read_bytes();sources[path]=sha(raw)
 pinned=subprocess.check_output(['git','-C',str(repo),'show','16a39d2a8a5124e25c787f2b9fcaf8449fb84611:'+path])
 assert pinned==raw,path
 if scope:
  raw,*_=cut.find_item(p,scope)
  with tempfile.NamedTemporaryFile() as f:
   f.write(raw);f.flush();body,*_=cut.find_item(Path(f.name),anchor)
 else:body,*_=cut.find_item(p,anchor)
 outputs['fragments/'+name+'.rs']=body;return body
field='crates/aspis-core/src/field.rs';wide='crates/aspis-core/src/field/wide_exact.rs';scalar='crates/aspis-core/src/r0/scalar.rs'
p=extract('p',field,'pub const P: u32')
types=b'\n'.join(extract(n,field,a) for n,a in [('m31','pub struct M31(pub u32)'),('cm31','pub struct CM31 {'),('qm31','pub struct QM31 {')])
wt=extract('wide',wide,'pub struct WideExact {')
consts={name:extract(name.lower()+'-zero',field,'pub const ZERO:',scope='impl '+name+' {') for name in ['M31','CM31','QM31']}
cm=extract('cm-from',field,'pub fn from_m31(a: M31)')
qm=extract('qm-from',field,'pub fn from_cm31(c0: CM31)')
canon=extract('canonical',wide,'fn canonical_qm31(value: QM31)')
wf=extract('wide-from',wide,'pub fn from_qm31(value: QM31)')
impls={name:extract(name.lower()+'-trait',scalar,'fn from_m31(value: M31)',scope='impl CodeField for '+name+' {') for name in ['M31','CM31','QM31','WideExact']}
trace=extract('trace','crates/aspis-r1-cost-probe/src/trace.rs','pub fn value(tag: u16')
lib=b'pub mod field {\n'+p+b'\n'+types+b'\n'+wt+b'\n'
for name in ['M31','CM31','QM31']:
 lib+=b'impl '+name.encode()+b' {\n'+consts[name]+b'\n'+(cm if name=='CM31' else qm if name=='QM31' else b'')+b'\n}\n'
lib+=canon+b'\nimpl WideExact {\n'+wf+b'\n}\n}\npub mod scalar {use crate::field::{M31,CM31,QM31,WideExact,P};\npub trait CodeField {fn from_m31(value:M31)->Self;}\n'
for name,body in impls.items():lib+=b'impl CodeField for '+name.encode()+b'{\n'+body+b'\n}\n'
lib+=b'}\npub mod trace {use crate::field::WideExact as E;\n'+trace+b'\n}\n'
lib+=b'pub fn from_m31(value:field::M31)->field::WideExact {<field::WideExact as scalar::CodeField>::from_m31(value)}\n'
outputs['lib.rs']=lib
outputs['Cargo.toml']=b'[package]\nname="aspis-r1-rho-diagnostics"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[features]\nprover=[]\n[workspace]\n'
outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-rho-diagnostics"\nversion = "0.0.0"\n'
pins=dict(candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611',features=[],source_sha256=sources,
 roots=['crate::field::_::from_qm31','crate::from_m31','crate::trace::value'],opaque_paths=[],
 kit_files={n:sha(b) for n,b in outputs.items()},
 scope='Dependency slice of exact unchanged constructor and non-prover trace bodies. Only from_m31 member of CodeField is retained; no other trait member or arithmetic implementation is consumed. Imports/module layout only. No constructor or trace argument evaluation is erased.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
 dest=here/'rho-diagnostics-input'/name
 if args.check:assert dest.read_bytes()==data,name
 else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
print(json.dumps(dict(check=args.check,source_bodies_unchanged=True,lib_sha256=sha(lib))))
