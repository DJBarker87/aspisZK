#!/usr/bin/env python3
"""Pin exact candidate-3 helpers, classifier and transport source items."""
from pathlib import Path
import subprocess,hashlib,json,re
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
base=Path(__file__).resolve().parents[5];tool=Path(__file__).resolve().parent
rev='d631a90ec0b75d2efbeaf62b7ee9c1ba9aac7ffe';old=subprocess.check_output(['git','-C',str(base),'rev-parse',rev+'^'],text=True).strip();sha=lambda b:hashlib.sha256(b).hexdigest();pins=[];out={}
def read(path,r=rev):return subprocess.check_output(['git','-C',str(base),'show',r+':'+path])
def item(src,start):
 a=src.index(start);b=src.index(b'{',a);d=1;e=b+1
 while d:d+=(src[e:e+1]==b'{')-(src[e:e+1]==b'}');e+=1
 return a,e,src[a:e]
def take(name,path,start,r=rev):
 src=read(path,r);a,e,data=item(src,start);pins.append(dict(kit_name=name,path=path,revision=r,start_byte=a,end_byte_exclusive=e,file_sha256=sha(src),fragment_sha256=sha(data)));return data
wp='crates/aspis-r1-cost-probe/src/weights.rs';tp='crates/aspis-r1-cost-probe/src/transport.rs'
for n,p in [('field.rs','crates/aspis-core/src/field.rs'),('field/wide_exact.rs','crates/aspis-core/src/field/wide_exact.rs'),('transport.rs',tp),('r0/transport.rs','crates/aspis-core/src/r0/transport.rs'),('r0/transport_pads.rs','crates/aspis-core/src/r0/transport_pads.rs')]:
 data=read(p);out[n]=data;pins.append(dict(kit_name=n,path=p,revision=rev,file_sha256=sha(data),fragment_sha256=sha(data),start_byte=0,end_byte_exclusive=len(data)))
struct=take('lib.rs',wp,b'pub struct Weights ');raw=take('lib.rs',wp,b'    pub fn raw(')
lib=b'extern crate self as aspis_core;\npub mod field;\npub mod transport;\nuse field::{QM31 as K,WideExact as E};\nuse transport::Variant;\n'+struct+b'\nimpl Weights {\n'+raw+b'\n}\npub mod old;\npub mod new;\npub mod r0;\n'
# Preserve raw source names, including TAU referenced by Variant.row (in transport).
out['lib.rs']=lib
err=take('r0/mod.rs','crates/aspis-core/src/r0/mod.rs',b'pub enum Error ')
out['r0/mod.rs']=b'#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+err+b'\npub const MESSAGE_LEN:usize=1024;\npub type Message<T>=[T;MESSAGE_LEN];\npub mod opening;\npub mod transport;\n'
opening=read('crates/aspis-core/src/r0/opening.rs');a=opening.index(b'pub const COPY_ACTIVE_ROW_MASKS');b=opening.index(b';',opening.index(b'=',a))+1;active=opening[a:b];pins.append(dict(kit_name='r0/opening.rs',path='crates/aspis-core/src/r0/opening.rs',revision=rev,start_byte=a,end_byte_exclusive=b,file_sha256=sha(opening),fragment_sha256=sha(active)))
inactive=take('r0/opening.rs','crates/aspis-core/src/r0/opening.rs',b'pub fn inactive(')
out['r0/opening.rs']=b'use super::Error;\n'+active+b'\n'+inactive+b'\n'
for side,r in [('old',old),('new',rev)]:
 data=read(wp,r);header=b'use crate::{Weights,transport::Variant,field::{QM31 as K,WideExact as E}};\n'
 field=take(side+'.rs',wp,b'pub fn field(',r);group=take(side+'.rs',wp,b'fn grouped_inactive_pair(',r)
 # Visibility is the only change to make private original methods extraction roots.
 group=group.replace(b'fn grouped_inactive_pair',b'pub fn grouped_inactive_pair',1)
 if side=='new':
  tables=b''
  for name in [b'S2_INACTIVE_GROUPS',b'S2_INACTIVE_MASKS']:
   a=data.index(b'const '+name);b=data.index(b';',data.index(b'=',a))+1;tables+=data[a:b]+b'\n';pins.append(dict(kit_name=side+'.rs',path=wp,revision=r,start_byte=a,end_byte_exclusive=b,file_sha256=sha(data),fragment_sha256=sha(data[a:b])))
  fast=take(side+'.rs',wp,b'fn s2_grouped_inactive_pair(',r).replace(b'fn s2_grouped_inactive_pair',b'pub fn s2_grouped_inactive_pair',1)
  header+=tables+fast+b'\n'
 out[side+'.rs']=header+field+b'\n'+group+b'\n'
out['Cargo.toml']=b'[package]\nname="aspis-r1-s2-groups"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n'
out['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-s2-groups"\nversion = "0.0.0"\n'
meta=dict(candidate=rev,parent=old,fragments=pins,scope='Exact selected source items; crate/module layout, explicit imports and public visibility only. Complete grouping helpers, raw classifier, row permutation and inactive function retained. Shared field arithmetic/decoder may be opaque computational parameters.',kit_files={n:sha(b) for n,b in out.items()})
out['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode();dest=tool/'s2-groups-input'
for n,b in out.items():
 p=dest/n
 if args.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(candidate=rev,parent=old,files=len(out))))
