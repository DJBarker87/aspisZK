#!/usr/bin/env python3
"""Complete current verify prefix over repinned canonical carriers and real boundaries."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
a=argparse.ArgumentParser();a.add_argument('--base-kit',type=Path,required=True);a.add_argument('--out',type=Path,required=True);a.add_argument('--check',action='store_true');a=a.parse_args();pins=json.loads((a.base_kit/'source-pins.json').read_text());rev=pins['revision'];base=(a.base_kit/'lib.rs').read_bytes();assert sha(base)==pins['kit_files']['lib.rs'];assert len(pins['cuts'])>=52
spec=importlib.util.spec_from_file_location('cut',H.parent/'public-serializer-extraction-kit/extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b
files={'base52/lib.rs':base,'base52/source-pins.json':(a.base_kit/'source-pins.json').read_bytes()};cuts=[]
def cut(name,path,anchor):
 raw=subprocess.check_output(['git','-C',str(R),'show',rev+':'+path]);b,start,end,first,last=m.find_item(Source(raw),anchor);files['fragments/'+name+'.rs']=b;cuts.append({'name':name,'path':path,'anchor':anchor,'source_file_sha256':sha(raw),'start_byte':start,'end_byte_exclusive':end,'start_line':first,'end_line_exclusive':last,'sha256':sha(b)});return b.decode()
s='crates/aspis-r1-cost-probe/src/r1_semantic.rs';v='crates/aspis-r1-cost-probe/src/verifier.rs'
verified=cut('verified',s,'pub struct Verified<H: Digest32>');mark=cut('semantic_mark',s,'fn mark(obs: crate::verifier::Observer, i: u8)');verify=cut('verify_observed',s,'#[inline(never)]\npub fn verify_observed<H: Digest32>');finish=cut('verify_finish',s,'fn verify_finish<H: Digest32>');phase=cut('phase',v,'pub enum Phase {');point=cut('secure_circle_point','crates/aspis-core/src/circle.rs','pub struct SecureCirclePoint')
lib=base.decode();lib=lib.replace('pub mod aspis_core {','pub mod aspis_core {\n pub mod circle {use super::field::QM31;\n'+point+'\n}',1)
lib=lib.replace('pub mod r1_semantic {','pub mod r1_semantic {\n use crate::r1_wire as wire; use crate::r1_wire::{Prefix,Challenges}; use alloc::boxed::Box; use crate::aspis_core::{circle::SecureCirclePoint,field::QM31};\n'+verified+'\n'+mark+'\n'+verify+'\n'+finish,1)
# Source finish references these arithmetic interfaces. They are cut at the
# existing whole function verify_finish and never interpreted from this kit.
# Rather than bringing a failed full tail dependency graph into this prefix,
# keep its complete source separately, and typecheck only its exact signature.
assert lib.count(finish)==1
signature=finish.split('{\n',1)[0]
finish_stub=signature+'{unreachable!()}'
lib=lib.replace(finish,finish_stub,1)
parse_stub="pub fn parse(_:&'a[u8])->Result<Self,Error>{unreachable!()}"
lib=lib.replace(" impl<'a> Prefix<'a> {", " impl<'a> Prefix<'a> {\n"+parse_stub,1)
lib+='\npub mod verifier {\n'+phase+'\npub type Observer=Option<fn(Phase)>;\n}\n'
files['lib.rs']=lib.encode();files['Cargo.toml']=b'[package]\nname="aspis-r1-verify-helper-prefix"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n[features]\nr0=[]\nprivate-leaf-salts=[]\ndetail-phases=[]\nprover=[]\n';files['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-verify-helper-prefix"\nversion = "0.0.0"\n'
record={'revision':rev,'base52_lib_sha256':sha(base),'base52_cuts':pins['cuts'],'base_source_files':pins['source_files'],'cuts':cuts,'features':['r0','private-leaf-salts'],'root_targets':['crate::r1_semantic::verify_observed'],'opaque_paths':['crate::r1_wire::_::parse','crate::r1_semantic::public_transcript','crate::r1_wire::begin','crate::r1_semantic::verify_finish'],'kit_files':{n:sha(b) for n,b in files.items()},'excluded_staging_bodies':{'verify_finish':{'actual_source_sha256':sha(finish.encode()),'staging_sha256':sha(finish_stub.encode()),'scope':'Actual complete source tail retained, only exact signature typechecked as explicitly opaque whole function. No stub behavior accepted.'},'Prefix.parse':{'staging_sha256':sha(parse_stub.encode()),'binding':'Must be fixed to accepted actual PrefixAdapter.parseAccepted and its current source repin; no arbitrary parse callback accepted in final caller theorem.'}},'scope':'Complete current actual verify_observed body and source semantic mark over current canonical carrier. Four existing function APIs cut; Prefix.parse/public_transcript/begin must be fixed to checked actual definitions, only verify_finish stays explicit universal tail. No opaque global axiom, no source/helper success premise.'}
files['source-pins.json']=(json.dumps(record,indent=2,sort_keys=True)+'\n').encode()
for n,b in files.items():
 p=a.out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps({'check':a.check,'revision':rev,'base_cuts':len(pins['cuts']),'new_source_cuts':len(cuts),'verify_sha256':sha(verify.encode()),'lib_sha256':sha(files['lib.rs'])}))
