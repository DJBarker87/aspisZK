from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-r1-cost-probe/src/verifier.rs';src=subprocess.check_output(['git','show',REV+':'+path],text=True)
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn k()->K{let x:[u32;4]=kani::any();K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn e()->E{E::new(k(),k())}
fn kw(x:K,j:usize)->u32{match j&3{0=>x.c0.a.0,1=>x.c0.b.0,2=>x.c1.a.0,_=>x.c1.b.0}}
fn ew(x:E,j:usize)->u32{kw(if j<4{x.c0()}else{x.c1()},j)}
fn prepared()->Prepared{Prepared{variant:Variant::S2,roots:kani::any(),gamma:e(),kappa:e(),alpha:[e(),e()],rho:k(),queries:kani::any(),semantic_alpha:[k(),k(),k(),k(),k(),k(),k(),k(),k(),k()],z:[SecureCirclePoint{x:k(),y:k()},SecureCirclePoint{x:k(),y:k()}],claim:e(),state:kani::any()}}
fn finish(p:Prepared,a:Accumulator,allocation:&mut usize)->Result<(Box<Prepared>,Accumulator),Error>{let boxed=Box::new(p);*allocation=boxed.as_ref() as *const Prepared as usize;Ok((boxed,a))}
fn check(){let p=prepared();let weights=alloc::vec::Vec::from([K::ZERO;64]);let pointer=weights.as_ptr() as usize;let capacity=weights.capacity();let a=Accumulator{weights,rhs:e(),power:k(),next:kani::any()};
 let roots=p.roots;let gamma=p.gamma;let kappa=p.kappa;let alpha=p.alpha;let rho=p.rho;let queries=p.queries;let semantic=p.semantic_alpha;let z=p.z;let claim=p.claim;let state=p.state;let rhs=a.rhs;let power=a.power;let next=a.next;
 let mut allocation=0;let (mut out,after)=finish(p,a,&mut allocation).unwrap();
 if cfg!(NIL_bad_box_value){out.variant=Variant::D;}if cfg!(NIL_bad_alloc){out=Box::new(prepared());}
 assert_eq!(out.as_ref() as *const Prepared as usize,allocation);
 let j:usize=kani::any();kani::assume(j<8);let b:usize=kani::any();kani::assume(b<32);let q:usize=kani::any();kani::assume(q<22);let sem:usize=kani::any();kani::assume(sem<10);let i:usize=kani::any();kani::assume(i<2);
 assert_eq!(out.variant,Variant::S2);assert_eq!(out.roots[i][b],roots[i][b]);assert_eq!(ew(out.gamma,j),ew(gamma,j));assert_eq!(ew(out.kappa,j),ew(kappa,j));assert_eq!(ew(out.alpha[i],j),ew(alpha[i],j));assert_eq!(kw(out.rho,j),kw(rho,j));assert_eq!(out.queries[q],queries[q]);assert_eq!(kw(out.semantic_alpha[sem],j),kw(semantic[sem],j));assert_eq!(kw(out.z[i].x,j),kw(z[i].x,j));assert_eq!(kw(out.z[i].y,j),kw(z[i].y,j));assert_eq!(ew(out.claim,j),ew(claim,j));assert_eq!(out.state[b],state[b]);assert_eq!(ew(after.rhs,j),ew(rhs,j));assert_eq!(kw(after.power,j),kw(power,j));assert_eq!(after.next,next);assert_eq!(after.weights.as_ptr() as usize,pointer);assert_eq!(after.weights.len(),64);assert_eq!(after.weights.capacity(),capacity);}
'''
for suffix in ['', '_renamed']:
 s+='#[kani::proof]\n#[kani::unwind(66)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn ctor'+suffix+'(){check();}\n'
inputs=json.loads((E/'NIL_NATIVE_INPUTS.json').read_text());assert 'mod NIL_ctor_native;' not in inputs[path];inputs[path]+='\n#[cfg(kani)]\n#[path="NIL_ctor_native.rs"]\nmod NIL_ctor_native;\n';inputs['crates/aspis-r1-cost-probe/src/NIL_ctor_native.rs']=s
(E/'NIL_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=2)+'\n');(E/'NIL_ctor_native.rs.txt').write_text(s)
pins=json.loads((E/'NIL_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in inputs.items()});(E/'NIL_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(E/'NIL_CTOR_PLAN.json').write_text(json.dumps({'family':'ctor','function':'verifier::NIL_ctor_native::ctor','rename':'verifier::NIL_ctor_native::ctor_renamed','domain':'SAME arbitrary Prepared fields at S2; owned Vec64 descriptor move; fixture zero bytes in Vec, no content observation/condition/access by finish; source move/frame identity still required to cover arbitrary contents','positive':'NIL_K084','control_value':'NIL_K085','control_allocation':'NIL_K086','rename_attempt':'NIL_K087','status':'planned','ruling':'aa; Kani own Box model; same allocation and exact projected payload; allocator abort retained, no fabricated recoverable Err'},indent=2)+'\n')
frag='Ok((Box::new(Prepared{variant:v,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state}),Accumulator{weights,rhs,power,next:bytes[9] as usize}))';assert frag in src
(E/'NIL_CTOR_CUT.json').write_text(json.dumps({'frozen':REV,'path':path,'fragment':frag,'fragment_sha256':hashlib.sha256(frag.encode()).hexdigest(),'changes':'payload assembly factored into typed arbitrary prestate p/a; let-bound Box for LOCAL allocation observation; exact same Box and accumulator returned. Vec content is not accessed; caller/source frame association remains required.'},indent=2)+'\n')
patch=''
for n,s in inputs.items():
 try:old=subprocess.check_output(['git','show',REV+':'+n],text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:old=''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NIL_native.patch').write_text(patch)
