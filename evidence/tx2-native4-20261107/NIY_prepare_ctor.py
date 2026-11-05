from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;P=E.parent/'tx2-native3-20261107';x=json.loads((E/'NIY_NATIVE_INPUTS.json').read_text());s=x['crates/aspis-r1-cost-probe/src/NIL_ctor_native.rs']
a=s.index('fn finish(');b=s.index('#[kani::proof]',a);s=s[:a]+'''fn finish(p:Prepared,mut a:Accumulator,end:usize,at2:usize,next:u8,allocation:&mut usize)->Result<(Box<Prepared>,Accumulator),Error>{
 if at2!=end{return Err(Error::Checkpoint);}
 a.next=next as usize;
 let boxed=Box::new(p);*allocation=boxed.as_ref() as *const Prepared as usize;Ok((boxed,a))
}
fn check(){
 let p=prepared();
 // Arbitrary valid prestate only; the map initializes the harness input, not a verifier loop.
 let raw=kani::vec::any_vec::<[u32;4],64>();kani::assume(raw.len()==64);
 let weights:alloc::vec::Vec<K>=raw.into_iter().map(|x|K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}).collect();
 let wi:usize=kani::any();kani::assume(wi<64);let j:usize=kani::any();kani::assume(j<8);
 let selected=kw(weights[wi],j);let pointer=weights.as_ptr() as usize;let capacity=weights.capacity();
 let a=Accumulator{weights,rhs:e(),power:k(),next:kani::any()};let next_byte:u8=kani::any();let end:usize=kani::any();let at2:usize=kani::any();
 let roots=p.roots;let gamma=p.gamma;let kappa=p.kappa;let alpha=p.alpha;let rho=p.rho;let queries=p.queries;let semantic=p.semantic_alpha;let z=p.z;let claim=p.claim;let state=p.state;let rhs=a.rhs;let power=a.power;
 let mut allocation=0;let result=finish(p,a,end,at2,next_byte,&mut allocation);
 if at2!=end{assert!(matches!(result,Err(Error::Checkpoint)));assert_eq!(allocation,0);return;}
 let (out,mut after)=result.unwrap();
 if cfg!(NIY_invert){after.weights[wi].c0.a.0^=1;after.weights[wi].c0.b.0^=1;after.weights[wi].c1.a.0^=1;after.weights[wi].c1.b.0^=1;}
 let b:usize=kani::any();kani::assume(b<32);let q:usize=kani::any();kani::assume(q<22);let sem:usize=kani::any();kani::assume(sem<10);let i:usize=kani::any();kani::assume(i<2);
 assert_eq!(out.as_ref() as *const Prepared as usize,allocation);
 assert_eq!(out.variant,Variant::S2);assert_eq!(out.roots[i][b],roots[i][b]);assert_eq!(ew(out.gamma,j),ew(gamma,j));assert_eq!(ew(out.kappa,j),ew(kappa,j));assert_eq!(ew(out.alpha[i],j),ew(alpha[i],j));assert_eq!(kw(out.rho,j),kw(rho,j));assert_eq!(out.queries[q],queries[q]);assert_eq!(kw(out.semantic_alpha[sem],j),kw(semantic[sem],j));assert_eq!(kw(out.z[i].x,j),kw(z[i].x,j));assert_eq!(kw(out.z[i].y,j),kw(z[i].y,j));assert_eq!(ew(out.claim,j),ew(claim,j));assert_eq!(out.state[b],state[b]);assert_eq!(ew(after.rhs,j),ew(rhs,j));assert_eq!(kw(after.power,j),kw(power,j));assert_eq!(after.next,next_byte as usize);assert_eq!(after.weights.as_ptr() as usize,pointer);assert_eq!(after.weights.len(),64);assert_eq!(after.weights.capacity(),capacity);assert_eq!(kw(after.weights[wi],j),selected);
}
'''
for suffix in ['', '_renamed']:
 s+='#[kani::proof]\n#[kani::unwind(66)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn ctor_payload'+suffix+'(){check();}\n'
(E/'NIY_ctor_payload.rs.txt').write_text(s)
path='crates/aspis-r1-cost-probe/src/verifier.rs';x[path]+='\n#[cfg(kani)]\n#[path="NIY_ctor_payload.rs"]\nmod NIY_ctor_payload;\n';x['crates/aspis-r1-cost-probe/src/NIY_ctor_payload.rs']=s
(E/'NIY_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=2)+'\n');pins=json.loads((E/'NIY_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(v.encode()).hexdigest() for n,v in x.items()});(E/'NIY_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
rows=json.loads((E/'NIY_NATIVE_MATRIX.json').read_text());old=rows[18];assert old['family']=='e664_1' and old['status']=='planned';(E/'NIY_DEFERRED_NATIVE.json').write_text(json.dumps([dict(**old,reason='Budget reassigned to remove the retained zero-weight restriction in the final Box/Vec facet; original NIL E664 value evidence remains qualified, new reader-frame facet is OPEN')],indent=2)+'\n')
rows[18]=dict(family='ctor_payload',function='verifier::NIY_ctor_payload::ctor_payload',rename='verifier::NIY_ctor_payload::ctor_payload_renamed',domain='S2 prepared fields arbitrary Rust-valid words; arbitrary valid Vec<K> length64; arbitrary end/at2/u8 next; complete final rejection/return fields, allocation/Vec descriptor and selected arbitrary payload cell',status='planned')
(E/'NIY_NATIVE_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';patch=''
for n,v in x.items():
 try:old=subprocess.check_output(['git','show',rev+':'+n],text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:old=''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),v.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NIY_native.patch').write_text(patch)
print('Added final Box/Vec payload family with arbitrary 64-cell weights, exact end guard and next-byte cast; source composition remains a separate obligation.')
