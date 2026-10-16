#!/usr/bin/env python3
"""Exact actual begin and opening hash operations; no source rewriting/stubs."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re,subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BASE=HERE.parent/'public-preparation-extraction-kit'
REV='c16ab4d76619cf2cf80ece9d7e60e47975957af0'
WIRE='crates/aspis-r1-cost-probe/src/r1_wire.rs'
FIELD='crates/aspis-core/src/field.rs'
SAMPLER='crates/aspis-r1-cost-probe/src/sampler.rs'
TRANS='crates/aspis-r1-cost-probe/src/transcript.rs'
TRANSPORT='crates/aspis-r1-cost-probe/src/transport.rs'
ITEMS=[
 ('cm31_type',FIELD,'pub struct CM31 {'),('qm31_type',FIELD,'pub struct QM31 {'),
 ('cm31_new',FIELD,'pub fn new(a: M31, b: M31) -> CM31'),('qm31_zero',FIELD,'pub const ZERO: QM31'),
 ('qm31_div_pass',SAMPLER,'fn qm31_div_pass('),('qm31_digits',SAMPLER,'fn qm31_digits('),('qm31_sample',SAMPLER,'pub fn qm31_sample('),
 ('challenges','crates/aspis-core/src/state_only_prefix.rs','pub struct Challenges {'),
 ('validated_type',WIRE,'pub(crate) struct ValidatedRecord'),('validated_row',WIRE,'pub(crate) fn row(&self)'),('validated_framed',WIRE,'pub(crate) fn framed(&self)'),
 ('prefix_type',WIRE,'pub struct Prefix'),('prefix_record',WIRE,'pub fn record(&self, row: u8)'),('prefix_validated_record',WIRE,'pub(crate) fn validated_record(&self, row: u8)'),
 ('semantic_validated',WIRE,'pub(crate) fn semantic_validated('),('begin',WIRE,'pub fn begin<H: Digest32>'),
 ('variant',TRANSPORT,'pub enum Variant {'),('variant_tag',TRANSPORT,'pub fn tag(self)'),
 ('opening_type',TRANS,'pub struct Transcript<H:'),('opening_new',TRANS,'pub fn new(hash:H'),('opening_absorb',TRANS,'pub fn absorb('),('opening_block',TRANS,'pub fn block('),
]
sha=lambda b:hashlib.sha256(b).hexdigest()
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b

def outputs():
 p=HERE.parent/'public-serializer-extraction-kit/extract.py'
 spec=importlib.util.spec_from_file_location('cutter',p);cutter=importlib.util.module_from_spec(spec);spec.loader.exec_module(cutter)
 basepins=json.loads((BASE/'source-pins.json').read_text());cuts=list(basepins['cuts']);sources={}
 fragments={q['name']:(BASE/'fragments'/(q['name']+'.rs')).read_bytes() for q in cuts}
 for q in cuts:
  raw=subprocess.check_output(['git','-C',str(ROOT),'show',REV+':'+q['path']]);sources[q['path']]=sha(raw)
  assert raw[q['start_byte']:q['end_byte_exclusive']]==fragments[q['name']],q['name']
 for name,path,anchor in ITEMS:
  raw=subprocess.check_output(['git','-C',str(ROOT),'show',REV+':'+path]);sources[path]=sha(raw)
  b,start,end,first,last=cutter.find_item(Source(raw),anchor)
  fragments[name]=b;cuts.append(dict(name=name,path=path,anchor=anchor,start_byte=start,end_byte_exclusive=end,start_line=first,end_line_exclusive=last,sha256=sha(b)))
 layout=(BASE/'layout.template.rs').read_text()
 layout=layout.replace('    pub mod field {','    pub mod field {\n        include!("fragments/cm31_type.rs");\n        include!("fragments/qm31_type.rs");\n        impl CM31 {\n            include!("fragments/cm31_new.rs");\n        }\n        impl QM31 {\n            include!("fragments/qm31_zero.rs");\n        }',1)
 layout=layout.replace('pub mod r1_wire {','pub mod sampler {\n use crate::aspis_core::field::{CM31,M31,P,QM31};\n include!("fragments/qm31_div_pass.rs");\n include!("fragments/qm31_digits.rs");\n include!("fragments/qm31_sample.rs");\n}\npub mod r1_wire {\n use crate::aspis_core::field::QM31;\n use crate::sampler::qm31_sample;\n include!("fragments/challenges.rs");\n include!("fragments/validated_type.rs");\n impl<\'a> ValidatedRecord<\'a> {\n include!("fragments/validated_row.rs");\n include!("fragments/validated_framed.rs");\n }\n include!("fragments/prefix_type.rs");\n impl<\'a> Prefix<\'a> {\n include!("fragments/prefix_record.rs");\n include!("fragments/prefix_validated_record.rs");\n }\n include!("fragments/begin.rs");',1)
 layout=layout.replace('        include!("fragments/transcript_step.rs");','        include!("fragments/transcript_step.rs");\n        include!("fragments/semantic_validated.rs");',1)
 layout=layout.replace('    // Extraction-only entry wrapper:', '''    pub fn semantic_validated_entry<H: Digest32>(transcript: &mut SemanticTranscript<H>, record: ValidatedRecord<'_>) -> Result<QM31, Error> { transcript.semantic_validated(record) }
    pub fn prefix_validated_entry<'a>(prefix: &Prefix<'a>, row: u8) -> Result<ValidatedRecord<'a>, Error> { prefix.validated_record(row) }
    // Extraction-only entry wrapper:''',1)
 layout+='\npub mod transport {\n include!("fragments/variant.rs");\n impl Variant {\n include!("fragments/variant_tag.rs");\n }\n}\npub mod transcript {\n use crate::aspis_core::Digest32;\n use crate::transport::Variant;\n include!("fragments/opening_type.rs");\n impl<H: Digest32> Transcript<H> {\n include!("fragments/opening_new.rs");\n include!("fragments/opening_absorb.rs");\n include!("fragments/opening_block.rs");\n }\n}\n'
 parts=[];spans=[];offset=0
 for line in layout.splitlines(keepends=True):
  m=re.fullmatch(r'\s*include!\("fragments/([a-z0-9_]+)\.rs"\);\n?',line)
  if m:
   name=m[1];part=fragments[name];spans.append(dict(name=name,start_byte=offset,end_byte_exclusive=offset+len(part),sha256=sha(part)));part+=b'\n' if not part.endswith(b'\n') else b''
  else:part=line.encode()
  parts.append(part);offset+=len(part)
 assert len(spans)==len(cuts) and {q['name'] for q in cuts}=={q['name'] for q in spans}
 out={f'fragments/{name}.rs':b for name,b in fragments.items()}
 out['layout.template.rs']=layout.encode();out['lib.rs']=b''.join(parts)
 out['Cargo.toml']=(BASE/'Cargo.toml').read_bytes();out['Cargo.lock']=(BASE/'Cargo.lock').read_bytes()
 pins=dict(revision=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',REV],text=True).strip(),source_files=sources,cuts=cuts,layout_spans=spans,features=['r0','private-leaf-salts'],kit_files={n:sha(b) for n,b in out.items()},scope='Actual unchanged begin, semantic_validated, Prefix accessors, opening constructor/absorb/block and existing preparation union. No handwritten transcript/caller, no stub. verify_observed, circle mapping and Prepared caller not included.')
 out['source-pins.json']=(json.dumps(pins,indent=2,sort_keys=True)+'\n').encode();return out

def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 out=outputs()
 for n,b in out.items():
  p=HERE/n
  if args.check:assert p.read_bytes()==b,n
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 print(json.dumps(dict(status='PASS',cuts=len(json.loads(out['source-pins.json'])['cuts']),lib_sha256=sha(out['lib.rs']),checked=args.check)))
if __name__=='__main__':main()
