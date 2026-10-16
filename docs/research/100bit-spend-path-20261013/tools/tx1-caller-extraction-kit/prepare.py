#!/usr/bin/env python3
"""Complete actual tx1 and verifier observer wrapper over canonical carriers."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
a=argparse.ArgumentParser();a.add_argument('--out',type=Path,required=True);a.add_argument('--revision',default='3335eecf2f2a08096abe95c67ac6b304f2df6284');a.add_argument('--check',action='store_true');a=a.parse_args()
spec=importlib.util.spec_from_file_location('cut',R/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b
base=H.parent/'verify-prepared-prefix-kit/input';files={str(p.relative_to(base)):p.read_bytes() for p in base.rglob('*') if p.is_file()};pins=json.loads(files.pop('source-pins.json'));old=files['lib.rs'].decode();source=old;cuts=[]
def cut(name,path,anchor):
 raw=subprocess.check_output(['git','-C',str(R),'show',a.revision+':'+path]);b,start,end,line,last=m.find_item(Source(raw),anchor);files['fragments/'+name+'.rs']=b;cuts.append(dict(name=name,path=path,source_file_sha256=sha(raw),start_byte=start,end_byte_exclusive=end,start_line=line,end_line_exclusive=last,sha256=sha(b)));return b.decode()
v='crates/aspis-r1-cost-probe/src/verifier.rs'
newprepare=cut('prepared_new',v,'#[inline(never)]\n    pub fn new<H:Digest32>');helper=cut('prepared_claim',v,'fn prepared_claim<H:Digest32>')
assert source.count((base/'fragments/prepared_new.rs').read_text())==1
source=source.replace((base/'fragments/prepared_new.rs').read_text(),newprepare,1).replace(' impl Prepared {',helper+'\n impl Prepared {',1)
acc=cut('accumulator',v,'pub struct Accumulator {');geometry=cut('query_geometry',v,'struct QueryGeometry {');tx1=cut('tx1',v,'#[inline(never)]\npub fn tx1<H:Digest32>');mark=cut('verifier_mark',v,'fn mark(obs:Observer,p:Phase)')
addition='''
impl<'a> View<'a> {pub fn parse(_:&'a[u8])->Result<Self,Error>{unreachable!()}}
'''+acc+'''\nimpl Accumulator {pub fn new(_:Variant)->Result<Self,Error>{unreachable!()}}\n'''+geometry+'''\nimpl QueryGeometry {fn for_range(_:&[u32;22],_:usize,_:usize)->Result<Self,Error>{unreachable!()}}
fn query_with_geometry<H:Digest32>(_:&View<'_>,_:&Prepared,_:&mut Accumulator,_:&[E;29],_:H,_:Observer,_:&QueryGeometry)->Result<(),Error>{unreachable!()}
pub fn checkpoint<H:Digest32>(_:&Prepared,_:&Accumulator,_:&[u8],_:&[u8],_:H)->Vec<u8>{unreachable!()}
'''+mark+'\n'+tx1+'\n'
needle='\n} }\npub fn prepared_entry';assert source.count(needle)==1;source=source.replace(needle,'\n}\n'+addition+'\n}\npub fn prepared_entry',1)
source=source.replace('pub mod verifier {','pub mod verifier {use crate::pool_v1::pair_forest_semantic_terminal::r0::Public; use crate::aspis_core::field::M31;',1)
files['lib.rs']=source.encode();files['Cargo.toml']=files['Cargo.toml'].replace(b'aspis-r1-verify-prepared-prefix',b'aspis-r1-tx1-caller');files['Cargo.lock']=files['Cargo.lock'].replace(b'aspis-r1-verify-prepared-prefix',b'aspis-r1-tx1-caller')
# Preserve inherited actual cuts; all unchanged source items are repinned below.
for c in pins['cuts']:
 if c['name']=='prepared_new':continue
 raw=subprocess.check_output(['git','-C',str(R),'show',a.revision+':'+c['path']]);b=files['fragments/'+c['name']+'.rs'];assert b in raw,c['name'];c['source_file_sha256']=sha(raw);start=raw.index(b);c['start_byte']=start;c['end_byte_exclusive']=start+len(b);c['start_line']=raw[:start].count(b'\n')+1;c['end_line_exclusive']=c['start_line']+b.count(b'\n')
pins['cuts']=[c for c in pins['cuts'] if c['name']!='prepared_new']+cuts;pins['base_revision']=pins['revision'];pins['revision']=a.revision
pins['opaque_paths']+=['crate::verifier::prepared_claim','crate::verifier::_::parse','crate::r1_semantic::verify_observed','crate::verifier::_::new','crate::verifier::_::for_range','crate::verifier::query_with_geometry','crate::verifier::checkpoint']
# Restrict new() opacity to Accumulator, keeping actual Prepared::new visible.
pins['opaque_paths'].remove('crate::verifier::_::new');pins['opaque_paths'].append('crate::verifier::{crate::verifier::Accumulator}::new')
pins['root_targets']=['crate::verifier::tx1'];pins['kit_files']={n:sha(b) for n,b in files.items()};pins['scope']='Complete unchanged tx1 and verifier mark bodies at approved Prepared revision. Current verify_observed, View.parse, allocation/math/query/checkpoint are explicit function boundaries; boundary stubs have no accepted semantics. No theorem may use opaque globals.'
files['source-pins.json']=(json.dumps(pins,indent=2,sort_keys=True)+'\n').encode()
for n,b in files.items():
 p=a.out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps({'check':a.check,'revision':a.revision,'cuts':len(pins['cuts']),'tx1_sha256':sha(tx1.encode()),'lib_sha256':sha(files['lib.rs'])}))
