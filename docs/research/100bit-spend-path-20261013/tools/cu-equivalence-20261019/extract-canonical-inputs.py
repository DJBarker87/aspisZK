#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,argparse
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest();rev='e58b87665233febecc1b1a75c506eac1a8b72e00'
def at(path):return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
outputs={};pins={}
for name in ['field.rs','field/wide_exact.rs']:
 path='crates/aspis-core/src/'+name;raw=at(path);outputs[name]=raw;pins[name]=dict(path=path,revision=rev,sha256=sha(raw))
path='crates/aspis-r1-cost-probe/src/weights.rs';raw=at(path);parts=[]
for anchor in [b'pub fn powers<const N:usize>',b'pub fn field(bytes:']:
 start=raw.index(anchor);body=raw.index(b'{',start);end=body+1;depth=1
 while depth:
  depth+=(raw[end]==123)-(raw[end]==125);end+=1
 parts.append(raw[start:end]);pins[anchor.decode()]=dict(path=path,revision=rev,file_sha256=sha(raw),start=start,end=end,sha256=sha(raw[start:end]))
outputs['weights.rs']=b'use crate::field::WideExact as E;\n'+b'\n'.join(parts)+b'\n'
outputs['lib.rs']=b'pub mod field;\npub mod weights;\n'
outputs['Cargo.toml']=b'[package]\nname="aspis-canonical-inputs"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n'
outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-canonical-inputs"\nversion = "0.0.0"\n'
outputs['source-pins.json']=(json.dumps(dict(candidate=rev,sources=pins,files={n:sha(v) for n,v in outputs.items()},scope='Exact full field files and whole field/powers functions; module boundary only. No algorithm changes.'),indent=2)+'\n').encode()
for n,b in outputs.items():
 target=here/'canonical-inputs-input'/n
 if a.check:assert target.read_bytes()==b,n
 else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
print(json.dumps(dict(check=a.check,files=len(outputs))))
