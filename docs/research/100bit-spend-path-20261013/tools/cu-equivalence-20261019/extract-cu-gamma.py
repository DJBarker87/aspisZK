#!/usr/bin/env python3
"""Paired complete claim/preparation bodies over shared exact source carriers."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];area=here.parents[1]
base_dir=area/'tools/prepared-actual-extraction-kit/input'
base=(base_dir/'lib.rs').read_bytes();bp=json.loads((base_dir/'source-pins.json').read_text())
sha=lambda raw:hashlib.sha256(raw).hexdigest()
assert sha(base)==bp['kit_files']['lib.rs']
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py')
cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
class Source:
 def __init__(self,raw):self.raw=raw
 def read_bytes(self):return self.raw
revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';candidate='3ab4faf7f5b488a0c82720717656a0ebf4c46efa'
ver='crates/aspis-r1-cost-probe/src/verifier.rs';sem='crates/aspis-r1-cost-probe/src/r1_semantic.rs'
outputs={};cuts=[]
def take(label,path,anchor,rev):
 raw=subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
 if rev==revision:assert raw==(repo/path).read_bytes(),path
 item,start,end,line,last=cut.find_item(Source(raw),anchor)
 outputs['fragments/'+label+'.rs']=item
 cuts.append(dict(label=label,path=path,revision=rev,file_sha256=sha(raw),start_byte=start,end_byte_exclusive=end,
  first_line=line,end_line_exclusive=last,sha256=sha(item)))
 return item
# These carriers are shared, not replaced by reduced diagnostic types.
for label,path,anchor,base_name in [
 ('prepared',ver,'pub struct Prepared {','prepared'),
 ('view',ver,"pub struct View<'a>",'view'),
 ('verified',sem,'pub struct Verified<H: Digest32>','verified'),
 ('error',ver,'#[derive(Debug,Clone,Copy,PartialEq,Eq)]\npub enum Error','verifier_error')]:
 item=take(label,path,anchor,revision)
 old=(base_dir/'fragments'/(base_name+'.rs')).read_bytes()
 assert base.count(old)==1,label
 base=base.replace(old,item)
 assert item==take(label+'-candidate',path,anchor,candidate),label
 assert item==take(label+'-reference',path,anchor,candidate+'^'),label
# Remove the historical changed functions, retaining their complete shared kit.
for name in ['prepared_claim','prepared_new']:
 old=(base_dir/'fragments'/(name+'.rs')).read_bytes();assert base.count(old)==1,name
 base=base.replace(old,b'')
root,*_=cut.find_item(Source(base),'pub fn prepared_entry<')
assert base.count(root)==1;base=base.replace(root,b'')
old_claim=take('old-claim',ver,'fn prepared_claim<H:Digest32>',candidate+'^')
new_claim=take('new-claim',ver,'fn prepared_claim<H:Digest32>',revision)
assert new_claim==take('new-claim-candidate',ver,'fn prepared_claim<H:Digest32>',candidate)
old_prepare=take('old-prepare',ver,'#[inline(never)]\n    pub fn new<H:Digest32>',candidate+'^')
new_prepare=take('new-prepare',ver,'#[inline(never)]\n    pub fn new<H:Digest32>',revision)
assert new_prepare==take('new-prepare-candidate',ver,'#[inline(never)]\n    pub fn new<H:Digest32>',candidate)
imports=b'''use alloc::{boxed::Box,vec::Vec};
use crate::{aspis_core::{Digest32,field::{WideExact as E,QM31 as K},circle::SecureCirclePoint},
 verifier::{Prepared,View,Error},transcript::Transcript,transport::Variant,weights::{powers,field}};
'''
for label,claim,prepare,method in [('old',old_claim,old_prepare,b'gamma_old_new'),('new',new_claim,new_prepare,b'gamma_new_new')]:
 assert prepare.count(b'pub fn new<')==1
 named=prepare.replace(b'pub fn new<',b'pub fn '+method+b'<',1)
 assert named.replace(b'pub fn '+method+b'<',b'pub fn new<',1)==prepare
 base+=b'\npub mod gamma_'+label.encode()+b' {\n'+imports+claim+b'\nimpl Prepared {\n'+named+b'\n}\n}\n'
base+=b'''
pub fn old_prepared_entry<H:aspis_core::Digest32>(sem:&r1_semantic::Verified<H>,v:&verifier::View<'_>,hash:H)->Result<alloc::boxed::Box<verifier::Prepared>,verifier::Error>{verifier::Prepared::gamma_old_new(sem,v,hash)}
pub fn new_prepared_entry<H:aspis_core::Digest32>(sem:&r1_semantic::Verified<H>,v:&verifier::View<'_>,hash:H,g:&mut [aspis_core::field::WideExact;29])->Result<alloc::boxed::Box<verifier::Prepared>,verifier::Error>{verifier::Prepared::gamma_new_new(sem,v,hash,g)}
'''
outputs['lib.rs']=base
outputs['Cargo.toml']=b'[package]\nname="aspis-r1-cu-gamma"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n[features]\nr0=[]\nprivate-leaf-salts=[]\ndetail-phases=[]\nprover=[]\n'
outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-cu-gamma"\nversion = "0.0.0"\n'
opaque=[p for p in bp['opaque_paths'] if p not in ['crate::verifier::prepared_claim','crate::fast_pairing','crate::weights']]
opaque+=['crate::weights::powers','crate::weights::field','crate::fast_pairing::_::new','crate::fast_pairing::_::push','crate::fast_pairing::_::finish',
 'crate::transcript::_::new','crate::transcript::_::scalar','crate::transcript::_::scalar_k','crate::r1_wire::_::state']
pins=dict(production_revision=revision,candidate=candidate,base_kit_lib_sha256=bp['kit_files']['lib.rs'],cuts=cuts,
 opaque_paths=opaque,features=['r0','private-leaf-salts'],kit_files={name:sha(data) for name,data in outputs.items()},
 layout_changes=['Shared exact carrier declarations from the retained prepared extraction kit, updated from pinned production declarations.',
 'Two complete claim bodies in separate lexical modules. Shared Prepared nominal carrier; only inherent new method identifiers are renamed old/new.',
 'One-call roots only; every selected production function body is unchanged.'],
 scope='Paired complete claim/preparation source emission. Shared unchanged callees must be explicit universal parameters or checked models; stubs and axiom templates are not theorem interpretations.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
 target=here/'cu-gamma-input'/name
 if args.check:assert target.read_bytes()==data,name
 else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
print(json.dumps(dict(check=args.check,cuts=len(cuts),complete_claims_and_preparation=True,lib_sha256=sha(base))))
