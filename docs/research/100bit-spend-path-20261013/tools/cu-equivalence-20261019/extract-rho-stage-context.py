#!/usr/bin/env python3
"""Factor exact transaction stage blocks, making owned-local handbacks explicit."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4];out=tool/'rho-stage-context-input';sha=lambda b:hashlib.sha256(b).hexdigest()
rev={'old':'a29133e2508d2f50a80e68d589259f2ba397da0e','new':'16a39d2a8a5124e25c787f2b9fcaf8449fb84611'}
path='crates/aspis-r1-cost-probe/src/verifier.rs'
def item(src,start):
 at=src.index(start);j=src.index(b'{',at);depth=1;k=j+1
 while depth:
  if src[k:k+1]==b'{':depth+=1
  elif src[k:k+1]==b'}':depth-=1
  k+=1
 return src[at:k]
lib=(tool/'rho-query-context-input/lib.rs').read_bytes()
lib+=b"\npub fn stage_query_old<H:Digest32>(v:&View<'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:H,obs:Observer,geometry:&QueryGeometry)->Result<(),Error>{unreachable!()}\npub fn stage_query_new<H:Digest32>(v:&View<'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:H,obs:Observer,geometry:&QueryGeometry,b:&mut BatchedWeights)->Result<(),Error>{unreachable!()}\n"
lib+=b'\nimpl BatchedWeights {pub fn new(_w:&[aspis_core::field::QM31])->Result<Self,Error>{unreachable!()} pub fn finish(&self,_w:&mut[aspis_core::field::QM31]) {unreachable!()}}\n'
outputs={};blocks={}
for side,r in rev.items():
 src=subprocess.check_output(['git','-C',str(repo),'show',r+':'+path]);blocks[side]={}
 for fn in ['tx1_finish','tx2','tx2_authenticated']:
  body=item(src,(b'fn ' if fn=='tx1_finish' else b'pub fn ')+fn.encode()+b'<')
  start=body.index(b'    let mut pending=' if side=='new' else b'    while a.next<')
  end=body.index(b'    let bytes=checkpoint(' if fn=='tx1_finish' else b'    finish_relation(')
  block=body[start:end];outputs[f'fragments/{side}-{fn}.rs']=body;outputs[f'fragments/{side}-{fn}-block.rs']=block;blocks[side][fn]=sha(block)
  canonical=block.replace(b'<k ',b'<end ')
  if fn=='tx1_finish':reference=canonical
  else:assert canonical.replace(b'<22 ',b'<end ')==reference
 # query's private a/pending handbacks are made explicit, matching emitted owned query roots.
 block=reference.replace(b'&v,&p,&mut a,&g',b'v,p,a,g').replace(b'&geometry',b'geometry')
 if side=='new':
  block=block.replace(b'query_with_geometry(v,p,a,g,hash,obs,geometry,Some(&mut pending))?;',b'crate::stage_query_new(v,p,&mut a,g,hash,obs,geometry,&mut pending)?;')
 else:block=block.replace(b'query_with_geometry(v,p,a,g,hash,obs,geometry)?;',b'crate::stage_query_old(v,p,&mut a,g,hash,obs,geometry)?;')
 signature=b'pub fn stage_'+side.encode()+b"<H:Digest32>(v:&View<'_>,p:&Prepared,mut a:Accumulator,g:&[E;29],hash:H,obs:Observer,geometry:&QueryGeometry,end:usize)->Result<Accumulator,Error> {\n"
 lib+=signature+block+b'    Ok(a)\n}\n'
outputs['lib.rs']=lib
for n in ['Cargo.toml','Cargo.lock']:outputs[n]=(tool/'rho-query-context-input'/n).read_bytes()
q=json.loads((tool/'rho-query-context-input/source-pins.json').read_text())
pins={'revisions':rev,'source_path':path,'stage_blocks_sha256':blocks,'scope':'Exact identical transaction stage blocks extracted; owned private accumulator and pending handbacks explicit at the already emitted owned query root. Initial new and final finish retained. Other transaction prefixes/suffixes remain separate.','opaque_paths':q['opaque_paths']+['crate::query_old::query_with_geometry','crate::query_new::query_with_geometry','crate::_::new','crate::_::finish','crate::stage_query_old','crate::stage_query_new'],'roots':['crate::stage_old','crate::stage_new'],'kit_files':{n:sha(b) for n,b in outputs.items()}}
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps({'check':a.check,'lib':sha(lib)}))
