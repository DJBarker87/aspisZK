from pathlib import Path
D=Path(__file__).resolve().parent;R=Path.cwd();O=D/'native';O.mkdir(exist_ok=True)
# Individual source modules are retained byte for byte in the test package.
for op in [36,134,205,212,215,216,217,219,226,249,250,252]:
 (O/f'op{op}.rs').write_bytes((D/'probes'/f'{op}.rs').read_bytes())
s='''#[path="op205.rs"] mod digest;
#[path="op252.rs"] mod weights;
#[path="op226.rs"] mod public;
#[path="op249.rs"] mod sampler;
#[path="op134.rs"] mod forest;
#[path="op36.rs"] mod adapter;
'''
s+='mod sha_checks {use super::digest::*;'+(D/'digest_checks.rs').read_text().split('mod checks {use super::*;',1)[1].rsplit('}',1)[0]+'}\n'
s+='''#[test] fn forest_inventory(){let masks=forest::active_row_masks().ok().unwrap();let mut hash=0xcbf29ce484222325u64;let mut count=0;for row in 0..1024 {if masks[row/16]&(1u16<<(row%16))!=0 {count+=1;for b in (row as u16).to_le_bytes(){hash=(hash^b as u64).wrapping_mul(0x100000001b3);}}}assert_eq!(count,214);assert_eq!(hash,0xdf394a5a8554d09c);}
#[test] fn owned_error_carrier(){let v=adapter::Buffer{data:[9u32,8,7,6],len:3};let e=adapter::array_try_from::<u32,2,4>(v,0).err().unwrap();assert_eq!(e.data,v.data);assert_eq!(e.len,3);let a=adapter::array_try_from::<u32,3,4>(v,0).ok().unwrap();assert_eq!(a,[9,8,7]);}
'''
# Exact shipped sampler source (through gamma, excluding unrelated circle).
o=(R/'crates/aspis-r1-cost-probe/src/sampler.rs').read_text();o=o[o.index('fn low_base_p_digits'):o.index('pub fn circle_sample')]
s+='mod original_sampler {use aspis_core::field::{WideExact,CM31,M31,P,QM31};'+o+'}\n'
s+='''#[test] fn sampler_differential(){for seed in 0..1024u32 {let mut block=[0u8;32];let mut x=seed.wrapping_add(1);for b in &mut block {x=x.wrapping_mul(1664525).wrapping_add(1013904223);*b=(x>>24) as u8;}assert_eq!(sampler::gamma_sample(&block),original_sampler::gamma_sample(&block));assert_eq!(sampler::ordinary_sample(&block),original_sampler::ordinary_sample(&block));}}
'''
# Preserve shipped weights loop body and allocating result for the native comparator.
w=(R/'crates/aspis-r1-cost-probe/src/weights.rs').read_text();a=w.index('        let points=',w.index('pub fn new('));b=w.index('\n    pub fn raw(',a);body=w[a:b];body=body[:body.rfind('\n    }')];body=body.replace('Ok(Self::box_from_parts(variant, factors, points, extra))','Ok(Box::new(Weights {variant,factors,points,extra}))')
s+='mod original_weights {use super::weights::{Weights,Variant,Error};use aspis_core::field::QM31 as K;use aspis_core::circle::SecureCirclePoint;const TAU:[usize;5]=[3,4,2,0,1];fn double(x:K)->K{x.mul(x).add(x.mul(x)).sub(K::ONE)}pub fn new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])->Result<Box<Weights>,Error>{'+body+'}}\n'
s+='''#[test] fn weights_differential(){use aspis_core::field::QM31 as K;use aspis_core::field::{M31,CM31};use aspis_core::circle::SecureCirclePoint;for seed in 0..64u32 {let mut alpha=[K::ZERO;10];for i in 0..10 {alpha[i]=K::from_cm31(CM31::from_m31(M31(seed*17+i as u32)));}let z=[SecureCirclePoint{x:alpha[0],y:alpha[1]},SecureCirclePoint{x:alpha[2],y:alpha[3]}];for v in [weights::Variant::S1,weights::Variant::S2,weights::Variant::D]{let a=weights::weights_new(v,&alpha,&z).ok().unwrap();let b=original_weights::new(v,&alpha,&z).ok().unwrap();assert_eq!(a.factors,b.factors);assert_eq!(a.points,b.points);assert_eq!(a.extra,b.extra);}}}
'''
# Independent Vec serializer has the shipped declaration order and canonicality failures.
s+='''fn old_public(p:public::Public)->Result<Vec<u8>,()>{fn fields(out:&mut Vec<u8>,v:&[u32])->Result<(),()>{for x in v {if *x>=2147483647{return Err(());}out.extend_from_slice(&x.to_le_bytes());}Ok(())}let mut out=vec![if p.withdrawal{1}else{0}];fields(&mut out,&p.anchor)?;fields(&mut out,&p.nullifier)?;fields(&mut out,&[p.asset_id])?;out.push(if p.withdrawal{0}else{1});if !p.withdrawal{fields(&mut out,&p.recipient)?;}fields(&mut out,&p.change)?;out.push(if p.withdrawal{1}else{0});if p.withdrawal{fields(&mut out,&[p.withdrawal_amount])?;}out.extend_from_slice(&p.next_pair_index.to_le_bytes());for x in p.frontier{fields(&mut out,&x)?;}fields(&mut out,&p.next_root)?;for x in p.next_frontier{fields(&mut out,&x)?;}Ok(out)}
#[test] fn public_bytes_differential(){for seed in 0..128u32 {for withdrawal in [false,true] {let mut p=public::Public{withdrawal,anchor:[seed;8],nullifier:[seed+1;8],asset_id:seed+2,recipient:[seed+3;8],change:[seed+4;8],withdrawal_amount:seed+5,next_pair_index:seed as u64,frontier:[[seed+6;8];20],next_root:[seed+7;8],next_frontier:[[seed+8;8];20]};for invalid in 0..8 {let old=old_public(p);let new=public::public_bytes(p);match (old,new){(Ok(a),Ok((b,n)))=>{assert_eq!(a,&b[..n]);assert_eq!(n,if withdrawal{1427}else{1455});},(Err(_),Err(_))=>(),_=>panic!("Result mismatch")};match invalid{0=>p.anchor[0]=2147483647,1=>{p.anchor[0]=seed;p.asset_id=2147483647},2=>{p.asset_id=seed;p.recipient[0]=2147483647},3=>{p.recipient[0]=seed;p.change[0]=2147483647},4=>{p.change[0]=seed;p.withdrawal_amount=2147483647},5=>{p.withdrawal_amount=seed;p.frontier[19][7]=2147483647},_=>{p.frontier[19][7]=seed;p.next_frontier[19][7]=2147483647}}}}}}
'''
s+='\n#[test] fn carrier_layouts(){assert_eq!(core::mem::size_of::<weights::Weights>(),2116);assert_eq!(core::mem::size_of::<digest::Sha256>(),112);assert_eq!(core::mem::size_of::<public::Public>(),1464);assert_eq!(core::mem::size_of::<adapter::Buffer<u32,4>>(),24);}\n'
(O/'lib.rs').write_text(s)
