#!/usr/bin/env python3
"""Factor complete original transaction callers at their checked stage block."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4];out=tool/'rho-transactions-input';sha=lambda b:hashlib.sha256(b).hexdigest()
rev={'old':'a29133e2508d2f50a80e68d589259f2ba397da0e','new':'16a39d2a8a5124e25c787f2b9fcaf8449fb84611'}
path='crates/aspis-r1-cost-probe/src/verifier.rs'
def item(src,start):
 at=src.index(start);j=src.index(b'{',at);depth=1;k=j+1
 while depth:
  if src[k:k+1]==b'{':depth+=1
  elif src[k:k+1]==b'}':depth-=1
  k+=1
 return src[at:k]
lib=(tool/'rho-stage-context-input/lib.rs').read_bytes()
lib+=b'''\nuse alloc::{boxed::Box,vec::Vec};
impl<'a> View<'a> {pub fn parse_shape(_bytes:&'a[u8])->Result<Self,Error>{unreachable!()}}
impl QueryGeometry {pub fn for_range(_q:&[u32;22],_s:usize,_e:usize)->Result<Self,Error>{unreachable!()}}
pub fn source_resume<H:Digest32>(_bytes:&[u8],_proof:&[u8],_public:&[u8],_v:transport::Variant,_hash:H)->Result<(Box<Prepared>,Accumulator),Error>{unreachable!()}
pub fn checkpoint<H:Digest32>(_p:&Prepared,_a:&Accumulator,_proof:&[u8],_public:&[u8],_hash:H)->Vec<u8>{unreachable!()}
pub fn finish_relation(_v:&View<'_>,_p:&Prepared,_a:&Accumulator,_obs:Observer)->Result<(),Error>{unreachable!()}
'''
outputs={};facts={}
for side,r in rev.items():
 src=subprocess.check_output(['git','-C',str(repo),'show',r+':'+path]);facts[side]={}
 lib+=b'pub mod tx_'+side.encode()+b' {use super::*;use crate::weights::powers;use crate::source_resume as resume;\n'
 for fn in ['tx1_finish','tx2','tx2_authenticated']:
  f=item(src,(b'fn ' if fn=='tx1_finish' else b'pub fn ')+fn.encode()+b'<')
  block=(tool/f'rho-stage-context-input/fragments/{side}-{fn}-block.rs').read_bytes();assert f.count(block)==1
  endpoint=b'k' if fn=='tx1_finish' else b'22'
  call=b'    a=crate::stage_'+side.encode()+b'(&v,&p,a,&g,hash,obs,&geometry,'+endpoint+b')?;\n'
  changed=f.replace(block,call,1);assert changed.replace(call,block,1)==f
  if fn=='tx1_finish':changed=changed.replace(b'fn tx1_finish<',b'pub fn tx1_finish<',1)
  lib+=changed+b'\n';outputs[f'fragments/{side}-{fn}.rs']=f;facts[side][fn]={'original_sha256':sha(f),'factored_sha256':sha(changed),'inverse_checked':True}
 lib+=b'}\n'
outputs['lib.rs']=lib
for n in ['Cargo.toml','Cargo.lock']:outputs[n]=(tool/'rho-stage-context-input'/n).read_bytes()
base=json.loads((tool/'rho-stage-context-input/source-pins.json').read_text())
pins=dict(revisions=rev,source_path=path,functions=facts,scope='Whole original transaction bodies, exact stage block substituted and inverse checked. Prefix, checkpoint/finish and diagnostic calls unchanged. Only the already checked stage receives private accumulator ownership.',opaque_paths=base['opaque_paths']+['crate::stage_old','crate::stage_new','crate::source_resume','crate::checkpoint','crate::finish_relation','crate::weights::powers','crate::_::for_range','crate::verifier::_::parse','crate::_::parse_shape'],roots=[f'crate::tx_{s}::{f}' for s in rev for f in ['tx1_finish','tx2','tx2_authenticated']],kit_files={n:sha(b) for n,b in outputs.items()})
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps({'check':a.check,'lib':sha(lib)}))
