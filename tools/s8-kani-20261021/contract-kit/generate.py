#!/usr/bin/env python3
"""Literal field layout/leaf bodies with research-only contract attributes.
The enclosing verifier/reference bodies are included unchanged from the main kit.
"""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[3];T=Path(__file__).resolve().parent
F=R/'crates/aspis-core/src/field.rs';s=F.read_text();items={}
def item(mark):
 a=s.index(mark);b=s.index('{',a);d=1;e=b+1
 while d:d+=(s[e]=='{')-(s[e]=='}');e+=1
 out=s[a:e];items[mark]=hashlib.sha256(out.encode()).hexdigest();return out
out='// Literal frozen field items; only contract attributes/Arbitrary derives added.\npub const P:u32=0x7fffffff;\n'
for name,decl in [('M31','pub struct M31(pub u32);'),('CM31',item('pub struct CM31')),('QM31',item('pub struct QM31'))]:
 out+='#[derive(Clone,Copy,PartialEq,Eq,Debug,Default)]\n#[cfg_attr(kani,derive(kani::Arbitrary))]\n'+decl+'\n'
out+=item('fn reduce_u64(x: u64)')+'\n'
for typ in ['M31','CM31','QM31']:
 out+='impl '+typ+' {\n'
 if typ=='M31':
  out+='#[cfg_attr(kani,kani::ensures(|r:&M31| r.0==crate::reduce_spec(value)))]\n'+item('pub fn reduce_u64(value: u64)')+'\n'
 out+=item('pub fn from_le_bytes(bytes: '+('[u8; 4]' if typ=='M31' else '&[u8]')+') -> Option<'+typ+'>')+'\n}\n'
p=T/'src/field.rs';E=R/'docs/research/100bit-spend-path-20261013/evidence/s8-kani-20261021/contract-kit-binding.json'
manifest={'field_source':str(F.relative_to(R)),'field_sha256':hashlib.sha256(s.encode()).hexdigest(),'literal_items':items,'adaptation':'Only local field structs derive Arbitrary and M31.reduce_u64 gets a verified contract attribute; source/reference S8 bodies included unchanged. No shipped files changed.','generated_sha256':hashlib.sha256(out.encode()).hexdigest()}
if '--check' in sys.argv:assert p.read_text()==out;assert json.loads(E.read_text())==manifest
else:p.write_text(out);E.write_text(json.dumps(manifest,indent=2)+'\n')
print('Local field layouts and leaf bodies match frozen source')
