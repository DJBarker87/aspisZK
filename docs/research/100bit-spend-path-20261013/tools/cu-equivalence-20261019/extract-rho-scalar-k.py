#!/usr/bin/env python3
"""Exact unchanged scalar_k caller with original sampler proof reuse boundary."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];area=here.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611';outputs={};identity=[]
for revision in ['3335eecf2f2a08096abe95c67ac6b304f2df6284',candidate+'^',candidate]:
 bodies={}
 for name,path,anchor in [('scalar-k','crates/aspis-r1-cost-probe/src/transcript.rs','pub fn scalar_k('),('transcript','crates/aspis-r1-cost-probe/src/transcript.rs','pub struct Transcript<'),('digest','crates/aspis-core/src/digest.rs','pub trait Digest32:')]:
  raw=subprocess.check_output(['git','-C',str(repo),'show',revision+':'+path])
  with tempfile.NamedTemporaryFile() as f:
   f.write(raw);f.flush();bodies[name],*_=cut.find_item(Path(f.name),anchor)
 if revision==candidate:
  for n,b in bodies.items():outputs['fragments/'+n+'.rs']=b
 identity.append(dict(revision=revision,body_sha256={n:sha(b) for n,b in bodies.items()}))
assert all(x['body_sha256']==identity[0]['body_sha256'] for x in identity)
sampler_identity=[]
for revision in ['670b7e149f94004baa5b138bdc2db28f3bc646bd',candidate+'^',candidate]:
 raw=subprocess.check_output(['git','-C',str(repo),'show',revision+':crates/aspis-r1-cost-probe/src/sampler.rs']);parts=[]
 with tempfile.NamedTemporaryFile() as f:
  f.write(raw);f.flush()
  for anchor in ['fn qm31_div_pass(','fn qm31_digits(','pub fn qm31_sample(']:
   body,*_=cut.find_item(Path(f.name),anchor);parts.append(sha(body))
 sampler_identity.append(dict(revision=revision,body_sha256=parts))
assert all(x['body_sha256']==sampler_identity[0]['body_sha256'] for x in sampler_identity)
fields=b'\n'.join((here/'rho-diagnostics-input/fragments'/n).read_bytes() for n in ['m31.rs','cm31.rs','qm31.rs','wide.rs'])
lib=outputs['fragments/digest.rs']+b'\npub mod field {\n'+fields+b'\nimpl WideExact {pub fn from_qm31(_q:QM31)->Self{unreachable!()}}\n}\npub mod aspis_core {pub use crate::{Digest32,field};}\npub mod sampler {pub fn qm31_sample(_block:&[u8;32])->crate::field::QM31{unreachable!()}}\npub mod trace {pub fn value(_tag:u16,_index:usize,_x:crate::field::WideExact){unreachable!()}}\npub mod transcript {use crate::{Digest32,aspis_core};use crate::field::WideExact as E;\n'+outputs['fragments/transcript.rs']+b'\nimpl<H:Digest32> Transcript<H> {pub fn block(&mut self,_row:u8,_payload:&[u8])->[u8;32]{unreachable!()}\n'+outputs['fragments/scalar-k.rs']+b'\n}\n}\n'
outputs.update({'lib.rs':lib,'Cargo.toml':b'[package]\nname="aspis-r1-rho-scalar-k"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n','Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-rho-scalar-k"\nversion = "0.0.0"\n'})
pins=dict(candidate=candidate,features=[],source_identity=identity,sampler_identity=sampler_identity,
 roots=['crate::transcript::_::scalar_k'],opaque_paths=['crate::transcript::_::block','crate::sampler::qm31_sample','crate::field::_::from_qm31','crate::trace::value'],kit_files={n:sha(b) for n,b in outputs.items()},scope='Complete unchanged scalar_k body with exact Transcript and Digest32 types. Shared block is universally parameterized; sampler binds to the existing checked exact sampler, constructors/trace to exact diagnostic source. No callback success or canonicality premise is invented.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=here/'rho-scalar-k-input'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,source_scalar_k_unchanged=True,sampler_source_identical=True)))
