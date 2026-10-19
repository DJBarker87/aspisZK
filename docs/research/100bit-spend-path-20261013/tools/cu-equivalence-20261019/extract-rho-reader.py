#!/usr/bin/env python3
"""Exact Reader::raw and Reader::k source for checkpoint canonicality."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
parser=repo/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py';spec=importlib.util.spec_from_file_location('cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611';source='crates/aspis-r1-cost-probe/src/verifier.rs'
outputs={};source_pins=[]
anchors={'error':'pub enum Error {','reader':"struct Reader<'a>",'raw':'fn raw<const N:usize>','k':'fn k(&mut self)'}
for revision in [candidate+'^',candidate,'39c2971dd16c95858a4cfd2c9ae35da052eacfa9']:
 raw=subprocess.check_output(['git','-C',str(repo),'show',revision+':'+source]);bodies={}
 with tempfile.NamedTemporaryFile() as f:
  f.write(raw);f.flush()
  for name,anchor in anchors.items():bodies[name],*_=cut.find_item(Path(f.name),anchor)
 source_pins.append(dict(revision=revision,source_sha256=sha(raw),fragments={n:sha(b) for n,b in bodies.items()}))
 if revision==candidate:
  for name,b in bodies.items():outputs['fragments/'+name+'.rs']=b
assert all(x['fragments']==source_pins[0]['fragments'] for x in source_pins)
field=b'\n'.join((here/'rho-input/fragments'/n).read_bytes() for n in ['m31.rs','cm31.rs','qm31.rs'])
lib=b'pub mod field {\n'+field+b'\nimpl QM31 {pub fn from_le_bytes(_bytes:&[u8])->Option<Self>{unreachable!()}}\n}\npub mod verifier {use crate::field::QM31 as K;\n'+outputs['fragments/error.rs']+b'\n'+outputs['fragments/reader.rs']+b"\nimpl<'a> Reader<'a> {\n"+outputs['fragments/raw.rs']+b'\n'+outputs['fragments/k.rs']+b'\n}\n}\n'
outputs.update({'lib.rs':lib,'Cargo.toml':b'[package]\nname="aspis-r1-rho-reader"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n','Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-rho-reader"\nversion = "0.0.0"\n'})
pins=dict(candidate=candidate,source=source,source_identity=source_pins,features=[],roots=['crate::verifier::_::k'],opaque_paths=['crate::field::_::from_le_bytes'],kit_files={n:sha(b) for n,b in outputs.items()},scope='Complete unchanged Reader declaration, raw const-array method and strict k method. Imports/module layout only; no method-body or visibility changes. Parser stub is opaque and must bind to the existing exact strict source decoder. Success theorem will not assume raw succeeds or bytes are canonical.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,b in outputs.items():
 p=here/'rho-reader-input'/name
 if a.check:assert p.read_bytes()==b,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,all_reader_bodies_unchanged=True,lib_sha256=sha(lib))))
