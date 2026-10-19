#!/usr/bin/env python3
"""Check a structural specialization; never rewrite the pinned next body."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent
raw=(here/'iterator-source/enumerate.rs').read_bytes()
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(raw)=='b64a625b876695472133816d411fc3fce3e2d5221178ff30a34370ab24ab9c95'
def item(anchor):
    start=raw.index(anchor);body=raw.index(b'{',start);depth=1;end=body+1
    while depth:
        depth+=(raw[end]==123)-(raw[end]==125);end+=1
    return start,body,end,raw[start:end]
ss,sb,se,struct=item(b'pub struct Enumerate<I>')
ns,nb,ne,next_method=item(b'fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>')
body=raw[nb:ne]
specialized=b'fn next(&mut self) -> Option<Self::Item> '+body
lib=struct+b'\nimpl<\'a,T> Iterator for Enumerate<core::slice::IterMut<\'a,T>> {\n'+\
    b'type Item = (usize, &\'a mut T);\n'+specialized+b'\n}\n'
outputs={'lib.rs':lib,
 'Cargo.toml':b'[package]\nname="aspis-cu-iterator"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n',
 'Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-cu-iterator"\nversion = "0.0.0"\n'}
manifest=dict(standard_source='iterator-source/enumerate.rs',standard_source_sha256=sha(raw),
 toolchain='nightly-2026-06-01',
 struct_cut=dict(start=ss,end=se,sha256=sha(struct)),
 next_cut=dict(start=ns,body_start=nb,end=ne,body_sha256=sha(body)),
 specialization=['I := core::slice::IterMut<\'a,T>',
  '<I as Iterator>::Item := &\'a mut T; Self::Item := (usize,&\'a mut T)',
  'Move the exact selected next body into this concrete trait implementation',
  'Keep struct and next body bytes unchanged; retain checked overflow profile'],
 omitted_attributes=['inline (code generation only)','rustc_inherit_overflow_checks (internal attribute; checks enabled explicitly)'],
 files={n:sha(b) for n,b in outputs.items()},
 scope='Selected IterMut specialization, not a generic Iterator proof. Generated source execution and model equality required; structural specialization remains an explicit trusted source-extraction boundary.')
outputs['source-pins.json']=(json.dumps(manifest,indent=2)+'\n').encode()
for name,data in outputs.items():
 p=here/'iterator-input'/name
 if a.check:assert p.read_bytes()==data,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=a.check,next_body_sha256=sha(body),lib_sha256=sha(lib))))
