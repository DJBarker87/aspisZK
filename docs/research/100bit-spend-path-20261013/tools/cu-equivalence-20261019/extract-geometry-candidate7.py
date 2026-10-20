#!/usr/bin/env python3
"""Exact geometry-cache front, accumulation-node prefix and dispatch extraction."""
from pathlib import Path
import argparse,json,hashlib,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4];out=tool/'geometry-candidate7-input';sha=lambda b:hashlib.sha256(b).hexdigest()
rev={'old':subprocess.check_output(['git','-C',str(repo),'rev-parse','2aa1b879c^'],text=True).strip(),'new':'2aa1b879c58a63fbc47df5a4662e808e261af41a'}
def read(r,p):return subprocess.check_output(['git','-C',str(repo),'show',r+':'+p])
base=tool/'canonical-dot-clients-input';files={x:(base/x).read_bytes()for x in ['field.rs','field/wide_exact.rs','Cargo.toml','Cargo.lock','verifier.rs']};files['Cargo.toml']=files['Cargo.toml'].replace(b'aspis-r1-cu-canonical-dots',b'aspis-r1-cu-geometry-candidate7');files['Cargo.lock']=files['Cargo.lock'].replace(b'aspis-r1-cu-canonical-dots',b'aspis-r1-cu-geometry-candidate7')
fd=read(rev['new'],'crates/aspis-r1-cost-probe/src/fast_domain.rs');files['fast_domain.rs']=fd
raw=read(rev['new'],'crates/aspis-core/src/r0/domain.rs');macro=raw[raw.index(b'macro_rules! index_type'):raw.index(b'index_type!(SlotIndex')];point=raw[raw.index(b'#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub struct Point'):raw.index(b'impl<E: CodeField> Point')];domain=b'use super::{Error,FIBRE_COUNT};\n'+macro+point
mod=read(rev['new'],'crates/aspis-core/src/r0/mod.rs');err=mod[mod.index(b'#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum Error'):mod.index(b'#[cfg(test)]')];files['domain.rs']=domain
files['lib.rs']=b'''extern crate self as aspis_core;
extern crate alloc;
pub mod field;pub mod fast_domain;pub mod verifier;
pub mod r0 {pub const FIBRE_COUNT:usize=1<<18;
'''+err+b'pub mod domain {include!("domain.rs");}}\nuse r0::domain;\npub mod old;pub mod new;\n'
# include! path underinline module resolvescrate source directory.
pins=[]
for side,r in rev.items():
 path='crates/aspis-r1-cost-probe/src/verifier.rs';src=read(r,path)
 begin=src.index(b'        if start>end||end>queries.len()');end=src.index(b'        if flat.is_empty()',begin);front=src[begin:end]
 output=b'        Ok(Front{flat,'+(b'denominators'if side=='old'else b'line_z_values')+b'})\n'
 field=b'denominators:Vec<[M31;5]>'if side=='old'else b'line_z_values:Vec<M31>'
 chunk=b'use crate::{field::M31,verifier::Error,domain};\nuse alloc::vec::Vec;\npub struct Front{pub flat:Vec<M31>,pub '+field+b'}\npub fn front(queries:&[u32;22],start:usize,end:usize)->Result<Front,Error>{\n'+front+output+b'}\n'
 node_start=src.index(b'    let mut node=crate::fast_domain::line_node(',src.index(b'pub fn accumulate('));node_end=src.index(b'    '+(b'let mut basis='if side=='old'else b'accumulate_with_node('),node_start);node=src[node_start:node_end];modified=node.replace(b'p.variant.folds()',b'folds');assert modified.replace(b'folds',b'p.variant.folds()')==node
 row_start=chunk.index(b'            let u=query as usize;');row_end=chunk.index(b'            flat.extend_from_slice(&values);',row_start);row=chunk[row_start:row_end];replacement=b'            let (values,line_z)=row(query)?;\n';factored=chunk[:row_start]+replacement+chunk[row_end:];assert factored.replace(replacement,row,1)==chunk
 chunk=factored+b'pub fn row(query:u32)->Result<([M31;5],M31),Error>{\n'+row+b'    Ok((values,line_z))\n}\n'
 files['fragments/'+side+'-row.rs']=row
 chunk+=b'pub fn node(folds:usize,index:usize)->M31{\n'+modified+b'    node\n}\n'
 if side=='new':
  pos=src.index(b'        let z=geometry.line_z[i-geometry.start];');fin=src.index(b'    } else {accumulate(',pos);dispatch=src[pos:fin];
  # Retain exact cache read and node expression, capture unchanged callee as caller context.
  expr=b'z.mul(z).double().sub(M31::ONE)';assert dispatch.count(expr)==1
  chunk+=b'pub fn cached_node(line_z:&[M31],i:usize,start:usize)->M31{\n        let z=line_z[i-start];\n        '+expr+b'\n}\n'
  files['fragments/new-dispatch.rs']=dispatch
 files[side+'.rs']=chunk;files['fragments/'+side+'-front.rs']=front;files['fragments/'+side+'-node.rs']=node
 pins.append(dict(side=side,revision=r,source_path=path,source_sha256=sha(src),front_start=begin,front_end=end,front_sha256=sha(front),node_start=node_start,node_end=node_end,node_sha256=sha(node),node_substitution={'old':'p.variant.folds()','new':'folds'},inverse_checked=True))
# Whole-function source context audit: only the cached node and dead row storage differ.
def item(src,token):
 start=src.index(token);j=src.index(b'{',start);depth=1;k=j+1
 while depth:
  if src[k:k+1]==b'{':depth+=1
  elif src[k:k+1]==b'}':depth-=1
  k+=1
 return src[start:k]
contexts={}
for side,r in rev.items():
 source=read(r,'crates/aspis-r1-cost-probe/src/verifier.rs')
 f=item(source,b'fn for_range(');offset=f.index(b'        if flat.is_empty()');tail=f[offset:]
 norm=tail.replace(b'denominators.len()',b'rows').replace(b'line_z_values.len()',b'rows').replace(b',line_z:line_z_values',b'')
 files['fragments/'+side+'-for-range.rs']=f;contexts[side]={'normalized_inverse_tail_sha256':sha(norm),'for_range_sha256':sha(f)}
 acc=item(source,b'pub fn accumulate(')
 tailacc=acc[acc.index(b'    let mut basis='):] if side=='old' else item(source,b'fn accumulate_with_node(').split(b'{',1)[1].lstrip(b'\n')
 contexts[side]['accumulation_tail_sha256']=sha(tailacc)
 files['fragments/'+side+'-accumulation-tail.rs']=tailacc
 q=item(source,b'fn query_with_geometry<');cut=q.index(b'    accumulate(p,a,u,folded);')if side=='old'else q.index(b'    if p.variant.folds()==2 {\n        // for_range already')
 contexts[side]['query_prefix_sha256']=sha(q[:cut]);files['fragments/'+side+'-query.rs']=q
 for fn in ['pub fn query<','fn tx1_finish<','pub fn tx2<','pub fn tx2_authenticated<']:
  full=item(source,fn.encode());files['fragments/'+side+'-'+fn.split()[1].split('<')[0]+'.rs']=full;contexts[side][fn]=sha(full)
 for rel in ['field.rs','field/wide_exact.rs','fast_domain.rs']:
  assert read(r,('crates/aspis-core/src/' if rel.startswith('field') else 'crates/aspis-r1-cost-probe/src/')+rel)==files[rel],(side,rel)
assert contexts['old']['normalized_inverse_tail_sha256']==contexts['new']['normalized_inverse_tail_sha256']
assert contexts['old']['accumulation_tail_sha256']==contexts['new']['accumulation_tail_sha256']
assert contexts['old']['query_prefix_sha256']==contexts['new']['query_prefix_sha256']
for fn in ['pub fn query<','fn tx1_finish<','pub fn tx2<','pub fn tx2_authenticated<']:assert contexts['old'][fn]==contexts['new'][fn]
files['source-pins.json']=(json.dumps(dict(candidate=rev['new'],parent=rev['old'],fragments=pins,whole_context_audit=contexts,fast_domain_sha256=sha(fd),domain_macro_sha256=sha(macro),domain_point_sha256=sha(point),scope='Exact original geometry row collection front; unchanged batch inversion tail retained as common computational continuation of flat+row-count. Exact accumulation-node prefix and new cache-read/step expression; accumulation tail and query prefix remain common contexts.',roots=['crate::old::front','crate::new::front','crate::old::row','crate::new::row','crate::old::node','crate::new::node','crate::new::cached_node'],opaque_paths=['crate::fast_domain::fibre_point','crate::fast_domain::line_node','crate::field::_::mul','crate::field::_::double','crate::field::_::sub'],kit_files={n:sha(b)for n,b in files.items()}),indent=2)+'\n').encode()
for n,b in files.items():
 p=out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,files=len(files),candidate=rev['new'])))
