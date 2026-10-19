#!/usr/bin/env python3
"""Freeze exact Option branch/residual bodies at the selected borrow types."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;raw=(here/'iterator-source/option.rs').read_bytes()
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(raw)=='7cf61204b05d98a95bc2e322d5fbfc1f4f91505109971917d9a7fb47151c50e6'
def body(anchor):
 start=raw.index(anchor);first=raw.index(b'{',start);end=first+1;depth=1
 while depth:
  depth+=(raw[end]==123)-(raw[end]==125);end+=1
 return raw[first:end],dict(start=start,body_start=first,end=end,sha256=sha(raw[first:end]))
branch,bpin=body(b'fn branch(self) -> ControlFlow<Self::Residual, Self::Output>')
residual,rpin=body(b'fn from_residual(residual: Option<convert::Infallible>) -> Self')
lib=b'''use core::ops::ControlFlow;
use core::convert::Infallible;
pub trait BorrowTry<'a,T> {
    fn branch(self) -> ControlFlow<Option<Infallible>, &'a mut T>;
}
impl<'a,T> BorrowTry<'a,T> for Option<&'a mut T> {
    fn branch(self) -> ControlFlow<Option<Infallible>, &'a mut T> '''+branch+b'''
}
pub fn from_residual<'a,T>(residual:Option<Infallible>) -> Option<(usize,&'a mut T)> '''+residual+b'\n'
outputs={'lib.rs':lib,
 'Cargo.toml':b'[package]\nname="aspis-cu-borrow-option"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n',
 'Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-cu-borrow-option"\nversion = "0.0.0"\n'}
pins=dict(source='iterator-source/option.rs',source_sha256=sha(raw),branch=bpin,from_residual=rpin,
 files={n:sha(b) for n,b in outputs.items()},
 specialization=['Option Try at Item := &mut T',
  'FromResidual return type := Option<(usize,&mut T)>',
  'Local trait/free function signatures avoid orphan rules; both bodies byte-identical'],
 scope='Concrete borrowed Option source models; structural specialization is an explicit trusted source-extraction boundary. No generic stdlib claim.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
 p=here/'borrow-option-input'/name
 if a.check:assert p.read_bytes()==data,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=a.check,lib_sha256=sha(lib))))
