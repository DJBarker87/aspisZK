#!/usr/bin/env python3
"""Inline exact Reader.k/raw bodies at the actual resume loop read call."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;kit=tool/'rho-resume-weights-input';out=tool/'rho-resume-inlined-input';sha=lambda b:hashlib.sha256(b).hexdigest()
s=(kit/'lib.rs').read_bytes()
raw=b'fn raw<const N:usize>(&mut self)->[u8;N] {let b=self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N;b}'
k=b'fn k(&mut self)->Result<K,Error>{K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)}'
assert raw in s and k in s
raw_body=raw.split(b'{',1)[1].rsplit(b'}',1)[0].replace(b'self',b'r').replace(b'N',b'16')
# The [u8;16] annotation carries the raw return type into the inlined block.
raw_body=raw_body.replace(b'let b=',b'let b:[u8;16]=',1)
read=b'{let __source_raw_16={'+raw_body+b'};K::from_le_bytes(&__source_raw_16).ok_or(Error::Checkpoint)}?'
old=b'for x in &mut weights {*x=r.k()?;}'
new=b'for x in &mut weights {*x='+read+b';}'
assert s.count(old)==1;rewritten=s.replace(old,new,1);assert rewritten.replace(new,old,1)==s
assert b'__source_raw_16' not in s
outputs={'lib.rs':rewritten}
for n in ['Cargo.toml','Cargo.lock']:outputs[n]=(kit/n).read_bytes()
pins={'original_kit':str(kit.name),'original_lib_sha256':sha(s),'original_reader_raw_sha256':sha(raw),'original_reader_k_sha256':sha(k),'original_loop_sha256':sha(old),'inline_loop_sha256':sha(new),'transport':['Exact source callee expansion: Reader.k then Reader.raw instantiated at N=16.','Receiver self -> r; explicit raw return type [u8;16] carried to local annotation; capture-free new local.','Original loop iterator/assignment/error propagation and whole owned-local helper remain unchanged. Inverse text substitution checked.','Production Rust is unchanged; no assumed Reader frame used for extraction.'],'kit_files':{n:sha(b) for n,b in outputs.items()}}
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(b)
print(json.dumps({'check':a.check,'lib_sha256':sha(rewritten)}))
