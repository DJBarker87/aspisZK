#!/usr/bin/env python3
"""Exact scalar-tower methods and old coefficient update, with shared callees opaque."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
parser=repo/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
field=repo/'crates/aspis-core/src/field.rs';raw=field.read_bytes()
revision='16a39d2a8a5124e25c787f2b9fcaf8449fb84611'
parent=subprocess.check_output(['git','-C',str(repo),'rev-parse',revision+'^'],text=True).strip()
assert raw==subprocess.check_output(['git','-C',str(repo),'show',revision+':crates/aspis-core/src/field.rs'])
old=subprocess.check_output(['git','-C',str(repo),'show',parent+':crates/aspis-r1-cost-probe/src/verifier.rs'])
assignment=b'a.weights[j]=a.weights[j].add(a.power.mul_m31(basis[j]));'
assert old.count(assignment)==1
outputs={};cuts=[]
for name,anchor in [('m31','pub struct M31(pub u32)'),('cm31','pub struct CM31 {'),('qm31','pub struct QM31 {'),
                    ('cm_mul_m31','pub fn mul_m31(self, rhs: M31) -> CM31 {'),
                    ('qm_mul_m31','pub fn mul_m31(self, rhs: M31) -> QM31 {')]:
    body,start,end,first,last=cut.find_item(field,anchor)
    outputs['fragments/'+name+'.rs']=body
    cuts.append(dict(name=name,path=str(field.relative_to(repo)),source_sha256=sha(raw),sha256=sha(body),start_byte=start,end_byte_exclusive=end))
lib=b'pub mod field {\n'+b'\n'.join(outputs['fragments/'+n+'.rs'] for n in ['m31','cm31','qm31'])
lib+=b'\nimpl M31 {pub fn mul(self,_rhs:Self)->Self {unreachable!()}}\nimpl CM31 {\n'+outputs['fragments/cm_mul_m31.rs']+b'\n}\n'
lib+=b'impl QM31 {pub fn add(self,_rhs:Self)->Self {unreachable!()}\n'+outputs['fragments/qm_mul_m31.rs']+b'\n}\n}\n'
# Bind only the three existing source lvalues; evaluation order is retained.
expression=assignment.removeprefix(b'a.weights[j]=').removesuffix(b';')
expression=expression.replace(b'a.weights[j]',b'weight').replace(b'a.power',b'power').replace(b'basis[j]',b'basis')
lib+=b'pub fn step(weight:field::QM31,power:field::QM31,basis:field::M31)->field::QM31 {\n'+expression+b'\n}\n'
outputs.update({'lib.rs':lib,'fragments/old-assignment.rs':assignment,'Cargo.toml':b'[package]\nname="aspis-r1-rho-reference-step"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n','Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-rho-reference-step"\nversion = "0.0.0"\n'})
pins=dict(candidate=revision,parent=parent,production_revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9',cuts=cuts,
          kit_files={n:sha(b) for n,b in outputs.items()},opaque_paths=['crate::field::_::mul','crate::field::_::add'],
          scope='Exact scalar-tower methods and old coefficient RHS. Existing shared M31.mul and QM31.add bind to original checked arithmetic bodies, never stub interpretations. Index reads/write and enclosing loop remain separate caller obligations.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
    p=here/'rho-reference-step-input'/name
    if a.check:assert p.read_bytes()==data,name
    else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=a.check,kit_sha256=sha(lib))))
