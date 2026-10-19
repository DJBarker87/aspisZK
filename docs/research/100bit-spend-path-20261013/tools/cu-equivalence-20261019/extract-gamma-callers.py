#!/usr/bin/env python3
"""Exact paired gamma-candidate tx1 wrappers; complete preparation is shared import."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
base_dir=here/'cu-gamma-input';pins=json.loads((base_dir/'source-pins.json').read_text())
base=(base_dir/'lib.rs').read_bytes();sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(base)==pins['kit_files']['lib.rs']
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py')
cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
class Source:
 def __init__(self,raw):self.raw=raw
 def read_bytes(self):return self.raw
path='crates/aspis-r1-cost-probe/src/verifier.rs';candidate=pins['candidate'];outputs={};cuts=[]
def take(label,anchor,rev):
 raw=subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
 item,start,end,line,last=cut.find_item(Source(raw),anchor)
 outputs['fragments/'+label+'.rs']=item
 cuts.append(dict(label=label,path=path,revision=rev,file_sha256=sha(raw),start_byte=start,end_byte_exclusive=end,first_line=line,end_line_exclusive=last,sha256=sha(item)))
 return item
acc=take('accumulator','pub struct Accumulator {',candidate)
assert acc==take('accumulator-reference','pub struct Accumulator {',candidate+'^')
mark=take('mark','fn mark(obs:Observer,p:Phase)',candidate)
assert mark==take('mark-reference','fn mark(obs:Observer,p:Phase)',candidate+'^')
# Test-only helpers are opaque at extraction; their source contracts are not
# interpreted as unreachable. Exact shared selected bodies remain archived.
finish=take('tx1-finish','#[inline(never)]\nfn tx1_finish<',candidate)
assert finish==take('tx1-finish-reference','#[inline(never)]\nfn tx1_finish<',candidate+'^')
finish_signature=finish[:finish.index(b'{')].replace(b'fn tx1_finish',b'pub fn tx1_finish',1)
extra=b'\n'+acc+b'\n'+mark.replace(b'fn mark',b'pub fn mark',1)+b'''
impl<'a> View<'a> {pub fn parse(_bytes:&'a[u8])->Result<Self,Error>{unreachable!()}}
impl Accumulator {pub fn new(_v:Variant)->Result<Self,Error>{unreachable!()}}
'''+finish_signature+b'{unreachable!()}\n'
anchor=b'\n impl Prepared {\n\n} }';assert base.count(anchor)==1;base=base.replace(anchor,extra+anchor)
for side,rev in [('old',candidate+'^'),('new',candidate)]:
 prepare=take(side+'-tx1-prepare','#[inline(never)]\nfn tx1_prepare<',rev)
 tx1=take(side+'-tx1','#[inline(never)]\npub fn tx1<',rev)
 named=prepare.replace(b'Prepared::new(',b'Prepared::gamma_'+side.encode()+b'_new(',1)
 assert named.replace(b'Prepared::gamma_'+side.encode()+b'_new(',b'Prepared::new(',1)==prepare
 module,*_=cut.find_item(Source(base),'pub mod gamma_'+side+' {')
 added=b'\nuse crate::verifier::{Accumulator,Observer,Phase,mark,tx1_finish};\nuse crate::pool_v1::pair_forest_semantic_terminal::r0::Public;\n'+named+b'\n'+tx1+b'\n'
 replacement=module[:-1]+added+b'}';assert base.count(module)==1;base=base.replace(module,replacement)
outputs['lib.rs']=base
for name in ['Cargo.toml','Cargo.lock']:outputs[name]=(base_dir/name).read_bytes()
opaque=pins['opaque_paths']+['crate::gamma_old::prepared_claim','crate::gamma_new::prepared_claim',
 'crate::gamma_old::_::gamma_old_new','crate::gamma_new::_::gamma_new_new',
 'crate::r1_semantic::verify_observed','crate::verifier::_::parse','crate::verifier::_::new','crate::verifier::tx1_finish']
metadata=dict(base_kit_lib_sha256=pins['kit_files']['lib.rs'],candidate=candidate,production_revision=pins['production_revision'],cuts=cuts,
 kit_files={name:sha(raw) for name,raw in outputs.items()},opaque_paths=opaque,
 features=['r0','private-leaf-salts'],layout_changes=['Reuse the pinned full gamma kit and exact carriers.',
 'Only rename Prepared::new calls to their paired inherent method identifiers. Complete tx1_prepare and tx1 bodies otherwise unchanged.',
 'Expose mark and tx1_finish at the test module boundary; the mark body is unchanged.',
 'View.parse, Accumulator.new, tx1_finish and semantic verification remain explicit shared source boundaries; no stub body is admitted.'],
 scope='Complete candidate-1 wrapper comparison. Caller composition must consume existing gamma preparation theorems; the claim-helper source equation remains open.')
outputs['source-pins.json']=(json.dumps(metadata,indent=2)+'\n').encode()
for name,raw in outputs.items():
 p=here/'cu-gamma-caller-input'/name
 if args.check:assert p.read_bytes()==raw,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
print(json.dumps(dict(check=args.check,cuts=len(cuts),lib_sha256=sha(base))))
