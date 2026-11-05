from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NIY_NATIVE_INPUTS.json').read_text())
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn kw(q:K,j:usize)->u32{match j{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
fn reserve_check(){
 let mut v:alloc::vec::Vec<K>=alloc::vec::Vec::new();let reply=v.try_reserve_exact(64);
 assert_eq!(v.len(),0);
 match reply{Ok(())=>assert_eq!(v.capacity(),64^(if cfg!(NIY_invert){1}else{0})),Err(_)=>assert_eq!(v.capacity(),0)}
}
fn step_check(){
 let raw:[[u32;4];64]=kani::any();
 let mut weights:alloc::vec::Vec<K>=alloc::vec::Vec::from(raw.map(|x|K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}));
 let bytes:[u8;1768]=kani::any();let i:usize=kani::any();kani::assume(i<64);let observed:usize=kani::any();kani::assume(observed<64);let j:usize=kani::any();kani::assume(j<4);
 let pointer=weights.as_ptr();let capacity=weights.capacity();let before=kw(weights[observed],j);let at=712+16*i;let mut reader=Reader{bytes:&bytes,at};
 // One actual iterator next, one actual Reader::k, and the exact source assignment.
 let mut it=weights[i..].iter_mut();let out=it.next().unwrap();let reply=reader.k();
 if let Ok(value)=reply{*out=value;}
 assert_eq!(it.len(),63-i);drop(it);
 if cfg!(NIY_invert){weights[observed].c0.a.0^=1;weights[observed].c0.b.0^=1;weights[observed].c1.a.0^=1;weights[observed].c1.b.0^=1;}
 assert_eq!(weights.as_ptr(),pointer);assert_eq!(weights.len(),64);assert_eq!(weights.capacity(),capacity);assert_eq!(reader.at,at+16);
 match reply{Ok(value)=>assert_eq!(kw(weights[observed],j),if observed==i{kw(value,j)}else{before}),Err(error)=>{assert_eq!(error,Error::Checkpoint);assert_eq!(kw(weights[observed],j),before);}}
}
'''
for name,call in [('reserve64','reserve_check();'),('weight_step','step_check();')]:
 for suffix in ['', '_renamed']:
  s+='#[kani::proof]\n#[kani::unwind(66)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn '+name+suffix+'(){'+call+'}\n'
n='crates/aspis-r1-cost-probe/src/NIY_weight_frame.rs';x[n]=s;v='crates/aspis-r1-cost-probe/src/verifier.rs';assert 'mod NIY_weight_frame;' not in x[v];x[v]+='\n#[cfg(kani)]\n#[path="NIY_weight_frame.rs"]\nmod NIY_weight_frame;\n'
(E/'NIY_weight_frame.rs.txt').write_text(s);(E/'NIY_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=2)+'\n');pins=json.loads((E/'NIY_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NIY_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
rows=json.loads((E/'NIY_NATIVE_MATRIX.json').read_text());deferred=json.loads((E/'NIY_DEFERRED_NATIVE.json').read_text())
for idx,name,domain in [(31,'reserve64','actual std try_reserve_exact64 from empty Vec<K>; both Result arms, no availability premise; actual filled source occurrence still requires installation'),(32,'weight_step','one actual iter_mut.next and Reader.k iteration at712+16*i, i<64; arbitrary64-cell Vec length/capacity64; observed cell0..63; descriptor/cursor/cell frame and Err branch; no whole loop')]:
 old=rows[idx];assert old['status']=='planned';deferred.append(dict(**old,reason='Replaced standalone reader facet by the real reserve/weight-loop caller dependency; actual Reader::k executes in the new step, retained NID/NIL callee laws remain'))
 rows[idx]=dict(family=name,function='verifier::NIY_weight_frame::'+name,rename='verifier::NIY_weight_frame::'+name+'_renamed',domain=domain,status='planned')
(E/'NIY_DEFERRED_NATIVE.json').write_text(json.dumps(deferred,indent=2)+'\n');(E/'NIY_NATIVE_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Prepared actual reserve64 producer checkpoint and one native weight-loop iteration with arbitrary prestate; replaced standalone callee probes.')
