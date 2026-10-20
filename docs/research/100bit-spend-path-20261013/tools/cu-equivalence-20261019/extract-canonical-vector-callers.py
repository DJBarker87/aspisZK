#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();here=Path(__file__).resolve().parent;repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest();rev='e58b87665233febecc1b1a75c506eac1a8b72e00';out={};pins={}
def at(path,r=rev):return subprocess.check_output(['git','-C',str(repo),'show',r+':'+path])
def block(raw,start):
 brace=raw.index(b'{',start);end=brace+1;depth=1
 while depth:depth+=(raw[end]==123)-(raw[end]==125);end+=1
 return end
for n in ['field.rs','field/wide_exact.rs']:
 path='crates/aspis-core/src/'+n;out[n]=at(path);pins[n]=dict(path=path,revision=rev,sha256=sha(out[n]))
for n,r in [('old_pairing.rs',rev+'^'),('new_pairing.rs',rev)]:
 path='crates/aspis-r1-cost-probe/src/fast_pairing.rs';out[n]=at(path,r);pins[n]=dict(path=path,revision=r,sha256=sha(out[n]))
vp='crates/aspis-r1-cost-probe/src/verifier.rs';v=at(vp);claim=v.index(b'fn prepared_claim');start=v.index(b'let mut dot=crate::fast_pairing::EbyKDot::new();',claim);loop=v.index(b'for l in 0..29',start);end=block(v,loop);chunk=v[start:end]
sstart=chunk.index(b'let scalar=match point');send=chunk.index(b';',sstart)+1;scalar=chunk[sstart:send];factored=chunk[:sstart]+b'let scalar=crate::claim_scalar(l);'+chunk[send:];assert factored.replace(b'let scalar=crate::claim_scalar(l);',scalar)==chunk
pins['claim_dot']=dict(path=vp,file_sha256=sha(v),revision=rev,start=start,end=end,sha256=sha(chunk),scalar_expression_sha256=sha(scalar),scalar_expression=scalar.decode(),factor='Hoist identical read-only scalar expression to universally quantified common callee. No reference to dot/g; original expression checked unchanged in parent and candidate.')
assert chunk in at(vp,rev+'^')
fp='crates/aspis-r1-cost-probe/src/fast_dots.rs';f=at(fp);start=f.index(b'let mut tail=EbyKDot::new();');loop=f.index(b'for term in 0..2',start);end=block(f,loop);tail=f[start:end];assert tail in at(fp,rev+'^')
pins['tail']=dict(path=fp,revision=rev,file_sha256=sha(f),start=start,end=end,sha256=sha(tail),factor='Exact whole initializer/head/2-term source loop; terminal tail.finish() stays the argument of unchanged outer value.add context.')
e_start=v.index(b'pub enum Error');e_end=block(v,e_start);enum=v[e_start:e_end]
for version in ['old','new']:
 body=b'use crate::field::{WideExact as E,QM31};\nuse crate::'+version.encode()+b'_pairing::EbyKDot;\nuse crate::Error;\npub fn claim_dot(g:&[E;29])->Result<E,Error>{\n'+factored.replace(b'crate::fast_pairing::',b'crate::'+version.encode()+b'_pairing::')+b'\nOk(dot.finish())\n}\npub fn tail(q:&[u8],g:&[E;29],slot:usize)->E {\n'+tail+b'\ntail.finish()\n}\n'
 out[version+'_callers.rs']=body
out['lib.rs']=b'extern crate self as aspis_core;\npub mod field;pub mod old_pairing;pub mod new_pairing;\n#[derive(Debug,Clone,Copy,PartialEq,Eq)]\n'+enum+b'\npub fn claim_scalar(_:usize)->field::QM31{unreachable!()}\npub mod old_callers;pub mod new_callers;\n'
out['Cargo.toml']=b'[package]\nname="aspis-canonical-vector-callers"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n';out['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-canonical-vector-callers"\nversion = "0.0.0"\n'
out['source-pins.json']=(json.dumps(dict(candidate=rev,sources=pins,files={n:sha(b) for n,b in out.items()}),indent=2)+'\n').encode()
for n,b in out.items():
 p=here/'canonical-vector-callers-input'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,files=len(out))))
