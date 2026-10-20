#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,argparse
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest();rev='e58b87665233febecc1b1a75c506eac1a8b72e00';out={};pins={}
def get(path):return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
def cut(path,anchor):
 raw=get(path);start=raw.index(anchor);body=raw.index(b'{',start);end=body+1;depth=1
 while depth:depth+=(raw[end]==123)-(raw[end]==125);end+=1
 b=raw[start:end];pins[anchor.decode()]=dict(path=path,revision=rev,file_sha256=sha(raw),start=start,end=end,sha256=sha(b));return b
for name in ['field.rs','field/wide_exact.rs']:
 path='crates/aspis-core/src/'+name;out[name]=get(path);pins[name]=dict(path=path,sha256=sha(out[name]),revision=rev)
digest=cut('crates/aspis-core/src/digest.rs',b'pub trait Digest32:')
tpath='crates/aspis-r1-cost-probe/src/transcript.rs';spath='crates/aspis-r1-cost-probe/src/sampler.rs'
lib=b'extern crate self as aspis_core;\npub mod field;\n'+digest+b'\npub mod sampler {use crate::field::{WideExact,CM31,M31,QM31};\nfn low_base_p_digits(_: &[u8;32])->([u32;8],u32){unreachable!()}\nfn add_small_base_p(_: &mut [u32;8],_:u32)->bool{unreachable!()}\n'+b'\n'.join(cut(spath,x) for x in [b'fn decode8(',b'pub fn ordinary_sample(',b'pub fn gamma_sample('])+b'\n}\npub mod trace {pub fn value(_:u16,_:usize,_:crate::field::WideExact){unreachable!()}}\npub mod transcript {use crate::{Digest32,field::WideExact as E};\n'+cut(tpath,b'pub struct Transcript<')+b'\nimpl<H:Digest32> Transcript<H> {pub fn block(&mut self,_:u8,_:&[u8])->[u8;32]{unreachable!()}\n'+cut(tpath,b'pub fn scalar(')+b'\n}}\n'
out['lib.rs']=lib;out['Cargo.toml']=b'[package]\nname="aspis-canonical-sampler"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n';out['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-canonical-sampler"\nversion = "0.0.0"\n'
out['source-pins.json']=(json.dumps(dict(candidate=rev,sources=pins,files={n:sha(v) for n,v in out.items()},scope='Whole unchanged scalar/gamma/ordinary/decode8 bodies and exact field source. Only identical source lowdigits/addsmall/block/trace computational leaves are opaque; canonicality follows from actual final constructor for arbitrary leaf outputs.'),indent=2)+'\n').encode()
for n,b in out.items():
 target=here/'canonical-sampler-input'/n
 if a.check:assert target.read_bytes()==b,n
 else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
print(json.dumps(dict(check=a.check,files=len(out))))
