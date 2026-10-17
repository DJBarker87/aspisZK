#!/usr/bin/env python3
"""Exact current query body, current52 carriers, explicit decoder/embedding boundary."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent;REV='1b98d3cf3';sha=lambda b:hashlib.sha256(b).hexdigest()
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b
spec=importlib.util.spec_from_file_location('cut',H.parent/'public-serializer-extraction-kit/extract.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();base=H/'base52';pins=json.loads((base/'source-pins.json').read_text());files={};cuts=[]
def cut(name,path,anchor):
 raw=subprocess.check_output(['git','-C',str(R),'show',REV+':'+path]);b,start,end,line,last=c.find_item(Source(raw),anchor);cuts.append(dict(name=name,path=path,source_file_sha256=sha(raw),start_byte=start,end_byte_exclusive=end,start_line=line,end_line_exclusive=last,sha256=sha(b)));files['fragments/'+name+'.rs']=b;return b.decode()
query=cut('opening_queries','crates/aspis-r1-cost-probe/src/transcript.rs','pub fn queries(&mut self,');err=cut('query_error','crates/aspis-core/src/transcript.rs','#[derive(Clone, Copy, PartialEq, Eq, Debug)]\npub enum QuerySampleError');wide=cut('wide','crates/aspis-core/src/field/wide_exact.rs','#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]\npub struct WideExact');vererr=cut('verifier_error','crates/aspis-r1-cost-probe/src/verifier.rs','#[derive(Debug,Clone,Copy,PartialEq,Eq)]\npub enum Error');trace=cut('trace_value','crates/aspis-r1-cost-probe/src/trace.rs','pub fn value(tag: u16,')
lib=(base/'lib.rs').read_text();lib=lib.replace('pub mod aspis_core {','pub mod aspis_core {\n pub mod transcript { '+err+' }\n pub mod r0_transcript {pub fn queries_from_pairs(_: &[[u8;32];8],_: &[[u8;32];8])->Result<([u32;22],[u8;32]),super::transcript::QuerySampleError>{unreachable!()} }',1);lib=lib.replace('    pub mod field {','    pub mod field {\n'+wide+'\n impl WideExact {pub fn from_m31(_:M31)->Self {unreachable!()}}',1)
# There are two transcript modules; add imports only at the opening module.
anchor='pub mod transcript {\n use crate::aspis_core::Digest32;';assert lib.count(anchor)==1;lib=lib.replace(anchor,'pub mod transcript {\n use crate::aspis_core; use crate::aspis_core::field::WideExact as E;\n use crate::aspis_core::Digest32;',1)
at=lib.rfind('\n}');assert at>=0;lib=lib[:at]+'\n impl<H:Digest32> Transcript<H> { '+query+' }\n'+lib[at:]
lib+='\npub mod verifier { '+vererr+' }\n pub mod trace { use crate::aspis_core::field::WideExact as E; '+trace+' }\n pub fn queries_entry<H:crate::aspis_core::Digest32>(mut transcript:crate::transcript::Transcript<H>,row:u8,payload:&[u8])->Result<[u32;22],crate::verifier::Error>{transcript.queries(row,payload)}\n'
files.update({'lib.rs':lib.encode(),'Cargo.toml':(base/'Cargo.toml').read_bytes(),'Cargo.lock':(base/'Cargo.lock').read_bytes()});new={'revision':REV,'base52_source_pins_sha256':sha((base/'source-pins.json').read_bytes()),'base52_cuts':pins['cuts'],'cuts':cuts,'features':['r0','private-leaf-salts'],'opaque_paths':['crate::aspis_core::r0_transcript::queries_from_pairs','crate::aspis_core::field::_::from_m31'],'kit_files':{n:sha(b)for n,b in files.items()},'scope':'Whole unchanged current queries body, byteexact copied; module/use layout only. Explicit pure decoder and embedding functions; neither stub behavior nor opaque axioms may be used.'};files['source-pins.json']=(json.dumps(new,indent=2,sort_keys=True)+'\n').encode()
for n,b in files.items():
 q=H/'queries'/n
 if a.check:assert q.read_bytes()==b,n
 else:q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
print(json.dumps({'status':'PASS','check':a.check,'lib_sha256':sha(files['lib.rs'])}))
