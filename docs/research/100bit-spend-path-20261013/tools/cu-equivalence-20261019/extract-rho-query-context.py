#!/usr/bin/env python3
"""Exact common source prefix factoring; no arithmetic or observable edits."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4];out=tool/'rho-query-context-input';sha=lambda b:hashlib.sha256(b).hexdigest()
rev={'old':'a29133e2508d2f50a80e68d589259f2ba397da0e','new':'16a39d2a8a5124e25c787f2b9fcaf8449fb84611'}
path='crates/aspis-r1-cost-probe/src/verifier.rs'
def item(src,start):
 at=src.index(start);j=src.index(b'{',at);depth=1;k=j+1
 while depth:
  if src[k:k+1]==b'{':depth+=1
  elif src[k:k+1]==b'}':depth-=1
  k+=1
 return src[at:k]
sources={s:subprocess.check_output(['git','-C',str(repo),'show',r+':'+path]) for s,r in rev.items()}
func={s:item(b,b'fn query_with_geometry<') for s,b in sources.items()}
boundary={'old':b'    if p.variant.folds()==2 {\n        // for_range','new':b'    let node=if p.variant.folds()==2 {'}
prefix={s:f[f.index(b'    let i=a.next;')+len(b'    let i=a.next;'):f.index(boundary[s])] for s,f in func.items()}
assert prefix['old']==prefix['new'];assert b'a.' not in prefix['new'] and b'pending' not in prefix['new']
common=b"fn source_query_prefix<H:Digest32>(v:&View<'_>,p:&Prepared,g:&[E;29],hash:H,obs:Observer,geometry:&QueryGeometry,i:usize)->Result<(usize,E),Error> {\n"+prefix['new']+b'    Ok((u,folded))\n}'
base=(tool/'rho-accumulate-factored-input/lib.rs').read_bytes()
lib=base+b'\nuse crate::{verifier::{View,Prepared,Accumulator,Error,Observer,Phase,mark},aspis_core::{Digest32,field::{WideExact as E,M31}}};\n'
geometry=item(sources['new'],b'struct QueryGeometry ');lib+=b'pub '+geometry+b'\n'
# Opaque common computation is represented by a type-correct extraction stub.
# Its body is NEVER admitted. Exact real prefix is pinned and shared by both callers.
stub=common[:common.index(b'{')]+b'{unreachable!()}'
lib+=stub+b'\n'
lib+=b'pub fn source_line_node(_u:usize)->M31 {unreachable!()}\n\n'
facts={}
wrapper=item(sources['old'],b'pub fn accumulate(')
expr=b'crate::fast_domain::line_node(domain::FibreIndex::new(if p.variant.folds()==1 {index}else{index/4*4}).unwrap())'
assert expr in wrapper
wbody=wrapper[wrapper.index(b'{')+1:wrapper.rindex(b'    accumulate_with_node(')]
wbody=wbody.replace(expr,b'crate::source_line_node(if p.variant.folds()==1 {index}else{index/4*4})')
oldnode=b'if p.variant.folds()==2 {\n let z=geometry.line_z[i-geometry.start];z.mul(z).double().sub(M31::ONE)\n } else { let index=u;'+wbody+b'node }'
newnode=func['new'][func['new'].index(b'    let node=')+len(b'    let node='):func['new'].index(b';\n    accumulate_with_node(')]
newnode=newnode.replace(b'crate::fast_domain::line_node(domain::FibreIndex::new(u).unwrap())',b'crate::source_line_node(u)')
for side,f in func.items():
 node=oldnode if side=='old' else newnode
 lib+=b'pub fn source_node_'+side.encode()+b'(p:&Prepared,geometry:&QueryGeometry,i:usize,u:usize)->M31 {'+node+b'}\n'
 start=f.index(boundary[side]);end=f.index(b'    mark(obs,Phase::Query(i));')
 call=b'let (u,folded)=crate::source_query_prefix(v,p,g,hash,obs,geometry,i)?;\n'
 suffix=b'    let node=crate::source_node_'+side.encode()+b'(p,geometry,i,u);\n    accumulate_with_node(p,a,node,folded'+(b',pending' if side=='new' else b'')+b');\n'
 changed=f[:start].replace(prefix[side],call,1)+suffix+f[end:]
 assert changed[:changed.index(suffix)].replace(call,prefix[side],1)==f[:start]
 assert changed[changed.index(suffix)+len(suffix):]==f[end:]
 changed=changed.replace(b'fn query_with_geometry<',b'pub fn query_with_geometry<',1)
 # The stage owns a and pending. Expose their actual source handbacks as owned locals.
 changed=changed.replace(b'a:&mut Accumulator',b'mut a:Accumulator',1)
 changed=changed.replace(b'pending:Option<&mut BatchedWeights>',b'mut pending:BatchedWeights',1)
 changed=changed.replace(b'accumulate_with_node(p,a,node,folded,pending)',b'accumulate_with_node(p,&mut a,node,folded,Some(&mut pending))')
 changed=changed.replace(b'accumulate_with_node(p,a,node,folded)',b'accumulate_with_node(p,&mut a,node,folded)')
 changed=changed.replace(b'->Result<(),Error>',b'->Result<'+(b'(Accumulator,BatchedWeights)' if side=='new' else b'Accumulator')+b',Error>',1)
 changed=changed.replace(b'Ok(())',b'Ok('+ (b'(a,pending)' if side=='new' else b'a')+b')')
 lib+=b'pub mod query_'+side.encode()+b' { use super::*; use crate::factored_'+side.encode()+b'::accumulate_with_node;\n'+changed+b'\n}\n'
 facts[side]={'original_sha256':sha(f),'factored_sha256':sha(changed),'node_continuation_factoring':'Old branches distribute the identical accumulate continuation; node expression has no mutable accumulator or pending input. Original accumulate wrapper inlined only for its node expression.','node_source_sha256':sha(node)}
outputs={'lib.rs':lib,'fragments/common-prefix.rs':common,'fragments/old-accumulate-wrapper.rs':wrapper,'fragments/old-node.rs':oldnode,'fragments/new-node.rs':newnode}
for s in func:outputs['fragments/'+s+'-query.rs']=func[s]
for n in ['Cargo.toml','Cargo.lock']:outputs[n]=(tool/'rho-accumulate-factored-input'/n).read_bytes()
basepins=json.loads((tool/'rho-accumulate-factored-input/source-pins.json').read_text())
pins={'revisions':rev,'source_path':path,'query':facts,'common_prefix_sha256':sha(common),'inverse_checked':True,'no_accumulator_or_pending_input_to_common_prefix':True,'scope':'Only exact whole common prefix extracted. Stub body never admitted; common computation is arbitrary and identical. Full original suffix, accumulation and mark retained.','opaque_paths':basepins['opaque_paths']+['crate::source_query_prefix','crate::factored_old::accumulate_with_node','crate::factored_new::accumulate_with_node','crate::verifier::mark','crate::source_line_node','crate::_::mul','crate::_::double','crate::_::sub'],'roots':['crate::query_old::query_with_geometry','crate::query_new::query_with_geometry','crate::source_node_old','crate::source_node_new'],'kit_files':{n:sha(b) for n,b in outputs.items()}}
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps({'check':a.check,'common_prefix':sha(common),'lib':sha(lib)}))
