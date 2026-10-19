#!/usr/bin/env python3
"""Exact paired accumulation bodies; unchanged arithmetic and checked push opaque."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
parser=repo/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611';parent=subprocess.check_output(['git','-C',str(repo),'rev-parse',candidate+'^'],text=True).strip()
source='crates/aspis-r1-cost-probe/src/verifier.rs';outputs={};sources={}
for side,revision in [('old',parent),('new',candidate)]:
    raw=subprocess.check_output(['git','-C',str(repo),'show',revision+':'+source]);sources[side]=sha(raw)
    # Existing extractor accepts paths; retain the complete pinned file as well.
    temporary=Path('/tmp/rho-accumulate-'+side+'-20261019.rs');temporary.write_bytes(raw)
    body,*_=cut.find_item(temporary,'fn accumulate_with_node(')
    outputs['fragments/'+side+'-accumulate.rs']=body
base=(here/'cu-gamma-caller-input/lib.rs').read_bytes()
pins=json.loads((here/'cu-gamma-caller-input/source-pins.json').read_text())
assert sha(base)==pins['kit_files']['lib.rs']
extra=b'''\nimpl aspis_core::field::M31 {
pub const ZERO:Self=Self(0);pub const ONE:Self=Self(1);
pub fn mul(self,_rhs:Self)->Self{unreachable!()}
pub fn sub(self,_rhs:Self)->Self{unreachable!()}
pub fn double(self)->Self{unreachable!()}
}
impl aspis_core::field::QM31 {pub fn mul_m31(self,_rhs:aspis_core::field::M31)->Self{unreachable!()}}
impl aspis_core::field::WideExact {pub fn mul_qm31(self,_rhs:aspis_core::field::QM31)->Self{unreachable!()}}
pub struct BatchedWeights {raw:alloc::vec::Vec<[u64;4]>,terms:usize}
impl BatchedWeights {
pub fn push(&mut self,_index:usize,_power:aspis_core::field::QM31,_basis:aspis_core::field::M31){unreachable!()}
pub fn value(&self,_index:usize)->aspis_core::field::QM31{unreachable!()}
}
'''
for side in ['old','new']:
    body=outputs['fragments/'+side+'-accumulate.rs']
    assert body.startswith(b'#[inline(never)]\nfn accumulate_with_node(')
    declared=body.replace(b'fn accumulate_with_node(',b'pub fn accumulate_with_node(',1)
    assert declared.replace(b'pub fn accumulate_with_node(',b'fn accumulate_with_node(',1)==body
    extra+=b'pub mod rho_'+side.encode()+b' {use crate::{verifier::{Prepared,Accumulator},aspis_core::field::{M31,WideExact as E},BatchedWeights};\n'+declared+b'\n}\n'
outputs['lib.rs']=base+extra
for name in ['Cargo.toml','Cargo.lock']:outputs[name]=(here/'cu-gamma-caller-input'/name).read_bytes()
opaque=pins['opaque_paths']+['crate::aspis_core::field::_::sub','crate::aspis_core::field::_::double',
    'crate::aspis_core::field::_::mul_m31','crate::aspis_core::field::_::mul_qm31','crate::_::push','crate::_::value']
meta=dict(candidate=candidate,parent=parent,source=source,source_sha256=sources,
    base_kit_lib_sha256=sha(base),features=['r0','private-leaf-salts'],opaque_paths=opaque,
    kit_files={n:sha(b) for n,b in outputs.items()},
    roots=['crate::rho_old::accumulate_with_node','crate::rho_new::accumulate_with_node'],
    scope='Complete paired original accumulation bodies, only visibility made public for root selection. Shared arithmetic and checked BatchedWeights.push/value remain explicit parameters; stubs are never source interpretations. No initialization or complete caller theorem is inferred from emission.')
outputs['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode()
for name,data in outputs.items():
    p=here/'rho-accumulate-input'/name
    if a.check:assert p.read_bytes()==data,name
    else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=a.check,lib_sha256=sha(outputs['lib.rs']))))
