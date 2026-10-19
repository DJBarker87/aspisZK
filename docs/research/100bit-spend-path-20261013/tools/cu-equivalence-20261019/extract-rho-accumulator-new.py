#!/usr/bin/env python3
"""Extract complete unchanged Accumulator.new and its actual length/constants."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611';outputs={};ident=[]
def item(raw,anchor):
 with tempfile.NamedTemporaryFile() as f:
  f.write(raw);f.flush();return cut.find_item(Path(f.name),anchor)[0]
for revision in [candidate+'^',candidate,'39c2971dd16c95858a4cfd2c9ae35da052eacfa9']:
 source=lambda path:subprocess.check_output(['git','-C',str(repo),'show',revision+':'+path])
 verifier=source('crates/aspis-r1-cost-probe/src/verifier.rs');transport=source('crates/aspis-r1-cost-probe/src/transport.rs');field=source('crates/aspis-core/src/field.rs');qm=item(field,'impl QM31 {');wide=source('crates/aspis-core/src/field/wide_exact.rs')
 fragments={'accumulator':item(verifier,'pub struct Accumulator {'),'new':item(verifier,'pub fn new(v:Variant)'),'error':item(verifier,'pub enum Error {'),'variant':item(transport,'pub enum Variant {'),'folds':item(transport,'pub fn folds(self)'),'final-len':item(transport,'pub fn final_len(self)'), 'zero':item(qm,'pub const ZERO: QM31'),'one':item(qm,'pub const ONE: QM31'),'wide-zero':item(wide,'pub const ZERO: Self'),'core-error':item(source('crates/aspis-core/src/r0/mod.rs'),'pub enum Error {')}
 ident.append(dict(revision=revision,fragment_sha256={n:sha(b) for n,b in fragments.items()}))
 if revision==candidate:
  outputs.update({'fragments/'+n+'.rs':b for n,b in fragments.items()});selected=fragments
assert all(x['fragment_sha256']==ident[0]['fragment_sha256'] for x in ident)
fields=b'\n'.join((here/'rho-diagnostics-input/fragments'/n).read_bytes() for n in ['m31.rs','cm31.rs','qm31.rs','wide.rs'])
s=selected
lib=b'extern crate alloc;\npub mod aspis_core {pub mod field {\n'+fields+b'\nimpl QM31 {\n'+s['zero']+b'\n'+s['one']+b'\n}\nimpl WideExact {\n'+s['wide-zero']+b'\n}\n}\npub mod r0 {\n'+s['core-error']+b'\npub mod heap {use alloc::vec::Vec;pub fn filled<T:Copy>(_length:usize,_value:T)->Result<Vec<T>,super::Error>{unreachable!()}}\n}}\npub mod transport {\n'+s['variant']+b'\nimpl Variant {\n'+s['folds']+b'\n'+s['final-len']+b'\n}}\npub mod verifier {use alloc::vec::Vec;use crate::{aspis_core::{self,field::{QM31 as K,WideExact as E}},transport::Variant};\n'+s['error']+b'\n'+s['accumulator']+b'\nimpl Accumulator {\n'+s['new']+b'\n}}\n'
outputs.update({'lib.rs':lib,'Cargo.toml':b'[package]\nname="aspis-r1-rho-accumulator-new"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n','Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-rho-accumulator-new"\nversion = "0.0.0"\n'})
pins=dict(candidate=candidate,source_identity=ident,features=[],roots=['crate::verifier::_::new'],opaque_paths=['crate::aspis_core::r0::heap::filled'],kit_files={n:sha(b) for n,b in outputs.items()},scope='Complete unchanged Accumulator.new, final_len/folds, constants and carriers. Imports/module layout only. Generic heap boundary binds to exact existing heap source. Success properties do not assume allocation succeeds or yields canonical entries.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=here/'rho-accumulator-new-input'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,whole_source_unchanged=True)))
