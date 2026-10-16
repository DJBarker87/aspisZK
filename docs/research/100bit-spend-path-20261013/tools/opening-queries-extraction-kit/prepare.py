#!/usr/bin/env python3
"""Exact unchanged whole query caller over accepted Prepared extraction carriers."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent;REV='96aad8ef209cb69d7667ab5d8728bd4584a86d16'
sha=lambda b:hashlib.sha256(b).hexdigest()
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b
p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
base=H.parent/'prepared-actual-extraction-kit/input';oldpins=json.loads((base/'source-pins.json').read_text());files={x:(base/x).read_bytes() for x in oldpins['kit_files']};cuts=[]
spec=importlib.util.spec_from_file_location('cut',R/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
def cut(name,path,anchor):
 raw=subprocess.check_output(['git','-C',str(R),'show',REV+':'+path]);b,start,end,line,last=m.find_item(Source(raw),anchor);cuts.append(dict(name=name,path=path,source_file_sha256=sha(raw),start_byte=start,end_byte_exclusive=end,start_line=line,end_line_exclusive=last,sha256=sha(b)));files['fragments/'+name+'.rs']=b;return b.decode()
queries=cut('opening_queries','crates/aspis-r1-cost-probe/src/transcript.rs','pub fn queries(&mut self,')
error=cut('query_sample_error','crates/aspis-core/src/transcript.rs','#[derive(Clone, Copy, PartialEq, Eq, Debug)]\npub enum QuerySampleError')
lib=files['lib.rs'].decode();stub='pub fn queries(&mut self,_:u8,_:&[u8])->Result<[u32;22],crate::verifier::Error> {unreachable!()}';assert lib.count(stub)==1;lib=lib.replace(stub,queries)
lib=lib.replace('pub mod aspis_core {','pub mod aspis_core {\n pub mod transcript { '+error+' }\n pub mod r0_transcript {pub fn queries_from_pairs(_: &[[u8;32];8],_: &[[u8;32];8])->Result<([u32;22],[u8;32]),super::transcript::QuerySampleError>{unreachable!()} }',1)
lib+='\npub fn queries_entry<H:crate::aspis_core::Digest32>(mut transcript:crate::transcript::Transcript<H>,row:u8,payload:&[u8])->Result<[u32;22],crate::verifier::Error>{transcript.queries(row,payload)}\n'
files['lib.rs']=lib.encode();pins=dict(oldpins);pins.update(revision=REV,base_prepared_source_pins_sha256=sha((base/'source-pins.json').read_bytes()),cuts=oldpins['cuts']+cuts,opaque_paths=[x for x in oldpins['opaque_paths'] if x!='crate::transcript::_::queries']+['crate::aspis_core::r0_transcript::queries_from_pairs'],scope='Exact whole unchanged opening queries caller. Pure decoder and field embedding are explicit boundaries; no Rustbehavior edits. Preserve returned decoder state, not eighth local advance.',kit_files={n:sha(b) for n,b in files.items()});files['source-pins.json']=(json.dumps(pins,indent=2,sort_keys=True)+'\n').encode()
for n,b in files.items():
 q=a.out/n
 if a.check:assert q.read_bytes()==b,n
 else:q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
print(json.dumps({'status':'PASS','check':a.check,'exact_newcuts':len(cuts),'lib_sha256':sha(files['lib.rs'])}))
