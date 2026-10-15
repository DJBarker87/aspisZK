#!/usr/bin/env python3
"""Render exact parser declaration cuts; namespace scaffolding only."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

KIT = Path(__file__).resolve().parent
ROOT = KIT.parents[4]
UTILITY = KIT.parent / 'public-serializer-extraction-kit/extract.py'
spec = importlib.util.spec_from_file_location('exact_declaration_cuts', UTILITY)
util = importlib.util.module_from_spec(spec)
spec.loader.exec_module(util)
WIRE = 'crates/aspis-r1-cost-probe/src/r1_wire.rs'
FIELD = 'crates/aspis-core/src/field.rs'
WIDE = 'crates/aspis-core/src/field/wide_exact.rs'
SHAPE = [
 ('lanes', WIRE, 'pub const LANES: usize'),
 ('points', WIRE, 'pub const POINTS: usize'),
 ('claims', WIRE, 'pub const CLAIMS: usize'),
 ('row_shape', WIRE, 'pub const fn row_shape(row: u8)'),
]
PARSER = [
 ('modulus', FIELD, 'pub const P: u32'),
 ('m31', FIELD, 'pub struct M31(pub u32)'),
 ('cm31', FIELD, 'pub struct CM31 {'),
 ('qm31', FIELD, 'pub struct QM31 {'),
 ('qm31_zero', FIELD, 'pub const ZERO: QM31'),
 ('wide_type', WIDE, 'pub struct WideExact {'),
 ('wide_limb_count', WIDE, 'pub const LIMB_COUNT: usize'),
 ('wide_byte_len', WIDE, 'pub const BYTE_LEN: usize'),
 ('wide_c1', WIDE, 'pub const fn c1(self) -> QM31'),
 ('wide_from_limbs', WIDE, 'pub fn from_limbs(limbs: [u32; Self::LIMB_COUNT])'),
 ('wide_from_le_bytes', WIDE, 'pub fn from_le_bytes(bytes: &[u8]) -> Option<Self>'),
 ('wire_error', WIRE, 'pub enum Error {'),
 ('validate_record_fields', WIRE, 'fn validate_record_fields(row: u8, payload: &[u8])'),
 ('parse_record', WIRE, 'pub fn parse_record(row: u8, record: &[u8])'),
]

def sha(data):
 return hashlib.sha256(data).hexdigest()

def main():
 ap=argparse.ArgumentParser()
 ap.add_argument('--target', choices=['row-shape','parse-record'], required=True)
 ap.add_argument('--check', action='store_true')
 args=ap.parse_args(); out=KIT/args.target
 items=SHAPE + (PARSER if args.target=='parse-record' else [])
 old=json.loads((out/'source-manifest.json').read_text()) if args.check else None
 revision=old['source_revision'] if old else subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()
 manifest={'format':1,'target':args.target,'source_revision':revision,
  'boundary':'Exact declarations and namespace/import scaffolding; no runtime refinement claim.',
  'cut_utility':{'path':str(UTILITY.relative_to(ROOT)), 'sha256':sha(UTILITY.read_bytes())},'items':[]}
 fragments={}
 for name,relative,anchor in items:
  src=ROOT/relative
  fragment,start,end,line_start,line_end=util.find_item(src,anchor)
  rev_source=subprocess.check_output(['git','-C',str(ROOT),'show',f'{revision}:{relative}'])
  fragments[name]=fragment
  manifest['items'].append({'name':name,'source_path':relative,'source_sha256':sha(src.read_bytes()),
   'source_revision_sha256':sha(rev_source),'anchor':anchor,'byte_start':start,'byte_end_exclusive':end,
   'line_start':line_start,'line_end_exclusive':line_end,'fragment_path':f'fragments/{name}.rs','fragment_sha256':sha(fragment)})
 template=(out/'layout.template.rs').read_text(); result=bytearray(); inserted=[]
 for line in template.splitlines(keepends=True):
  match=re.fullmatch(r'\s*include!\("fragments/([a-z0-9_]+)\.rs"\);\n?',line)
  if not match:result.extend(line.encode());continue
  name=match[1];fragment=fragments[name];start=len(result);result.extend(fragment)
  inserted.append({'name':name,'byte_start':start,'byte_end_exclusive':len(result),'sha256':sha(fragment)})
  if not fragment.endswith(b'\n'):result.extend(b'\n')
 assert len(inserted)==len(items) and {x['name']for x in inserted}==set(fragments)
 manifest['rendered_layout']={'path':'lib.rs','sha256':sha(result),'inserted_fragment_spans':inserted}
 outputs={f'fragments/{name}.rs':data for name,data in fragments.items()}
 outputs['lib.rs']=bytes(result)
 outputs['source-manifest.json']=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode()
 for name,data in outputs.items():
  p=out/name
  if args.check:assert p.read_bytes()==data, f'source cut mismatch: {name}'
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 names=['Cargo.toml','layout.template.rs',*outputs]
 pins={'format':1,'sources':{name:{'sha256':sha((out/name).read_bytes())} for name in sorted(names)}}
 encoded=(json.dumps(pins,indent=2,sort_keys=True)+'\n').encode()
 if args.check:assert (out/'source-pins.json').read_bytes()==encoded
 else:(out/'source-pins.json').write_bytes(encoded)
 print(f'{args.target}: {len(items)} exact source spans '+('verified' if args.check else 'prepared'))

if __name__=='__main__':main()
