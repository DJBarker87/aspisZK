#!/usr/bin/env python3
"""Exact original std-body adapters, with audited receiver renaming only."""
from pathlib import Path
import hashlib,json,argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
outputs={};pins={}
for name,anchor,signature in [
 ('slice-iter-macros.rs',b'fn all<F>(&mut self, mut f: F) -> bool',b"pub fn all<'a,T,F>(iter:&mut core::slice::Iter<'a,T>,mut f:F)->bool where F:FnMut(&'a T)->bool "),
 ('option.rs',b'pub const fn ok_or<E: [const] Destruct>(self, err: E)',b'pub fn ok_or<T,E>(value:Option<T>,err:E)->Result<T,E> ')]:
 raw=(here/'canonical-stdlib-source'/name).read_bytes();start=raw.index(anchor);body_start=raw.index(b'{',start);end=body_start+1;depth=1
 while depth:
  depth+=(raw[end]==123)-(raw[end]==125);end+=1
 body=raw[body_start:end];replacement=b'iter' if name.startswith('slice') else b'value';adapted=body.replace(b'self',replacement)
 assert adapted.replace(replacement,b'self')==body
 outputs[name+'.cut']=body
 outputs[name+'.adapter']=signature+adapted+b'\n'
 pins[name]=dict(source_sha256=sha(raw),start=start,body_start=body_start,end=end,body_sha256=sha(body),adapter_sha256=sha(signature+adapted+b'\n'),changes=['receiver self renamed to explicit parameter','generic method owner types materialized in signature; body unchanged modulo receiver renaming'])
lib=b''.join(v for k,v in outputs.items() if k.endswith('.adapter'))
outputs['lib.rs']=lib
outputs['Cargo.toml']=b'[package]\nname="aspis-canonical-stdlib"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n'
outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-canonical-stdlib"\nversion = "0.0.0"\n'
outputs['source-pins.json']=(json.dumps(dict(toolchain='nightly-2026-06-01',sources=pins,files={k:sha(v) for k,v in outputs.items()}),indent=2)+'\n').encode()
for name,data in outputs.items():
 p=here/'canonical-stdlib-input'/name
 if args.check:assert p.read_bytes()==data,name
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=args.check,files=len(outputs))))
