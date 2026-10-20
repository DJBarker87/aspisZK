#!/usr/bin/env python3
"""Pin complete original candidate-14 Libra source helpers."""
from pathlib import Path
import subprocess,hashlib,json
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4]
rev='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';old=subprocess.check_output(['git','-C',str(repo),'rev-parse',rev+'^'],text=True).strip();sha=lambda b:hashlib.sha256(b).hexdigest();pins=[];out={}
def read(p,r=rev):return subprocess.check_output(['git','-C',str(repo),'show',r+':'+p])
def take(p,start,r=rev):
 src=read(p,r);a=src.index(start);b=src.index(b'{',a);d=1;e=b+1
 while d:d+=(src[e:e+1]==b'{')-(src[e:e+1]==b'}');e+=1
 data=src[a:e];pins.append(dict(path=p,revision=r,start_byte=a,end_byte_exclusive=e,file_sha256=sha(src),fragment_sha256=sha(data)));return data
wp='crates/aspis-r1-cost-probe/src/weights.rs'
for n,p in [('field.rs','crates/aspis-core/src/field.rs'),('field/wide_exact.rs','crates/aspis-core/src/field/wide_exact.rs')]:
 data=read(p);out[n]=data;pins.append(dict(path=p,revision=rev,start_byte=0,end_byte_exclusive=len(data),file_sha256=sha(data),fragment_sha256=sha(data)))
header=b'use crate::field::{QM31 as K,WideExact as E,M31};\npub const QUARTER:M31=M31(536870912);\npub const PERM:[usize;4]=[0,3,2,1];\n'
assert header[header.index(b'pub const QUARTER'): ] in read(wp)
lib=b'extern crate self as aspis_core;\npub mod field;\npub mod old;\npub mod new;\n'+header+b'pub struct Weights;\nimpl Weights {\n'+take(wp,b'    fn scalar_factor(').replace(b'fn scalar_factor',b'pub fn scalar_factor',1)+b'\n}\n'+take(wp,b'pub fn kpowers<')+b'\n'
out['lib.rs']=lib
out['old.rs']=header+take(wp,b'fn twofold_libra_weights(',old).replace(b'fn twofold',b'pub fn twofold',1)+b'\n'
out['new.rs']=header+b'use crate::{Weights,kpowers};\n'+take(wp,b'fn factored_s2_libra_weights(').replace(b'fn factored',b'pub fn factored',1)+b'\n'
out['Cargo.toml']=b'[package]\nname="aspis-r1-libra"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n'
out['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-libra"\nversion = "0.0.0"\n'
meta=dict(candidate=rev,parent=old,fragments=pins,scope='Exact complete Libra helpers, scalar_factor and kpowers bodies. Module/import layout and private visibility only.',kit_files={n:sha(b) for n,b in out.items()})
out['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode()
for n,b in out.items():
 p=tool/'libra-input'/n
 if args.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=args.check,files=len(out),candidate=rev,parent=old)))
