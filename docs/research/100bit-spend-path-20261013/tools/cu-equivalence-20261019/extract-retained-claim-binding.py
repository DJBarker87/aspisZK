#!/usr/bin/env python3
"""Exact prepared_claim outer context after already audited inner-dot fission."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;repo=tool.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
subprocess.run(['python3',str(tool/'check-canonical-vector-context.py'),'--check'],check=True,capture_output=True)
source=(tool/'canonical-vector-context-audit/claim-context.factored.rs').read_bytes();body=source[source.index(b'{')+1:-1]
# Captured immutable sem/y1 inputs are used only inside the exact extracted dot helper.
assert b'sem'not in body and b'y1'not in body
body=body.replace(b'SOURCE_CLAIM_DOT(point,g)',b'crate::claim_dot(point,g)')
body=body.replace(b'crate::trace::value',b'crate::trace_value')
parts=body[body.index(b'        let mut parts='):body.index(b'        let mut claim=')]
sum_body=body[body.index(b'        let mut claim='):].replace(b'Ok(claim)',b'claim')
body=b'let k=powers::<7>(kappa);let parts=claim_parts(inactive,g)?;Ok(claim_sum(&k,&parts))'
base=tool/'canonical-vector-callers-input';files={n:(base/n).read_bytes()for n in ['field.rs','field/wide_exact.rs']}
enum=b'pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }'
files['lib.rs']=b'''extern crate self as aspis_core;
pub mod field;
use field::WideExact as E;
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
'''+enum+b'''
pub fn powers<const N:usize>(_:E)->[E;N]{unreachable!()}
pub fn claim_dot(_:usize,_:&[E;29])->Result<E,Error>{unreachable!()}
pub fn trace_value(_:u8,_:usize,_:E){}
pub fn claim_context(inactive:E,g:&[E;29],kappa:E)->Result<E,Error>{
'''+body+b'\n}\npub fn claim_parts(inactive:E,g:&[E;29])->Result<[E;7],Error>{\n'+parts+b'Ok(parts)\n}\npub fn claim_sum(k:&[E;7],parts:&[E;7])->E{\n'+sum_body+b'\n}\n'
files['Cargo.toml']=b'[package]\nname="aspis-retained-claim-binding"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n';files['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-retained-claim-binding"\nversion = "0.0.0"\n'
pins=dict(candidate='e58b87665233febecc1b1a75c506eac1a8b72e00',parent='e58b87665233febecc1b1a75c506eac1a8b72e00^',factored_context_sha256=sha(source),inverse_context_audit_sha256=sha((tool/'canonical-vector-context-audit/source-pins.json').read_bytes()),scope='Exact complete outer6 dot-calls +7 traced sum context; immutable sem/y1 captures lifted only into source helper; inner29 body already inverse audited. Actual powers and old/new dot functions supplied by source binding, not equivalence assumptions.',roots=['crate::claim_parts','crate::claim_sum','crate::claim_context'],opaque_paths=['crate::powers','crate::claim_dot','crate::trace_value','crate::field::wide_exact::_::add','crate::field::wide_exact::_::mul'],kit_files={n:sha(b)for n,b in files.items()})
files['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in files.items():
 p=tool/'retained-claim-binding-input'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,exact_outer_context=True,files=len(files))))
