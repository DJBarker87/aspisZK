//! Radius diagnostic for the actual research relation suffix.
//! Correct codeword point/OOD/inactive claims; semantic rounds opaque.
//! This file does NOT claim a full payment-semantic proof.
use super::*;
use super::{fixtures as f,inactive_binding as row};
extern crate aspis_statement as statement;
use statement::pool_v1::*;
const S:usize=9302;
fn changed(mut r:Vec<u8>)->Vec<u8>{
    for slot in 0..4{let bit=31*(32+4*slot);r[403+bit/8]|=1<<(bit%8);}r
}
fn c2tree()->f::Tree{
    let a=private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&changed(vec![0;REC])[403..589],&[0;32]);
    let b=private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&[0;186],&[0;32]);
    let mut t=vec![(0..1<<18).map(|i|if i<S{a}else{b}).collect::<Vec<_>>()];
    for _ in 0..18{t.push(t.last().unwrap().chunks_exact(2).map(|v|node_hash_v7(hash,&v[0],&v[1])).collect());}t
}
fn build(seed:u32,a:&f::Tree,b:&f::Tree,row_error:K)->(Vec<u8>,usize,usize){
    let mut v=vec![K::ZERO;697];let empty=vec![0;Q*REC];
    let stub=f::body(&v,a,b,&empty,(&[],&[]));let w=parse(&stub).unwrap();
    let s=row::semantic(&w,seed,true).unwrap();
    let mut u=vec![K::ZERO;1024];u[4]=K::ONE; // T2(x) in low-bit natural basis
    for (j,z) in corelib::v6_transcript::v6_statement_points(&s.z).iter().enumerate(){
        v[271+29*j]=statement::multilinear_evaluate_qm31(&u,z).unwrap();
    }
    v[271+28]=row_error; // actual D component polynomial is zero
    let mut inactive=WeightAccumulator::empty(10);
    inactive.add_grouped_64x16_binary_masks_deferred_prepared(
        pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1(),
        pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1()).unwrap();
    v[358]=inactive.weight_at(4);
    let stub=f::body(&v,a,b,&empty,(&[],&[]));let w=parse(&stub).unwrap();
    let mut t=row::semantic(&w,seed,true).unwrap().t;row::points_absorb(&mut t,&w);
    let z0=t.challenge_secure_circle_point().unwrap();v[359]=z0.x.square().mul_m31(M31(2)).sub(K::ONE);
    let mut rec=vec![0];rec.extend(bytes(&v[359..388]));t.absorb(V8_COMPONENT_OOD_VECTOR,&rec);
    let z1=(0..3).map(|_|t.challenge_secure_circle_point().unwrap()).find(|z|*z!=z0).unwrap();
    v[388]=z1.x.square().mul_m31(M31(2)).sub(K::ONE);
    let stub=f::body(&v,a,b,&empty,(&[],&[]));let w=parse(&stub).unwrap();
    let(mut p,ordinary,mut claim,kappa)=row::prepare(row::semantic(&w,seed,true).unwrap(),&w,true).unwrap();
    assert_eq!(p.points,[z0,z1]);let q=f::quotient(2,&p);
    assert_eq!(claim.sub(dot(&ordinary,&q)),kappa.mul(p.gamma.pow(28)).mul(row_error));
    // Corruption was committed in D before semantic/OOD challenges; its
    // virtual change is gamma^28/L, not a retrospectively chosen word.
    assert_ne!(p.gamma.pow(28),K::ZERO);
    let changed_ids:Vec<u32>=(0..S as u32).collect();
    let changed_points=corelib::circle_fri::selected_circle_fiber_points_shared(20,&changed_ids).unwrap();
    for pt in &changed_points{
        for(x,y)in [(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)]{
            assert_ne!(p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y)),K::ZERO);
        }
    }
    let mut weights=WeightAccumulator::empty(10);weights.add_dense(ordinary).unwrap();
    let mut image=vec![K::ZERO;1024];image[1023]=p.tau;image[1022]=p.tau.square().mul(p.abc[1]);image[1021]=p.tau.square().mul(p.abc[2]).neg();
    weights.add_dense(image).unwrap();
    f::save_round(&mut v,0,polynomial_for_extension(&q,&weights));
    let first=compact(&v[417..423],claim);absorb_round(&mut p.t,0,&first);
    p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&[0;9]);let alpha=sample(&mut p.t,false).unwrap();
    claim=evaluate(&first,alpha);weights.fold_deferred_relation_arity4(alpha);
    let mut finals=primal(&q,alpha);v[441..697].copy_from_slice(&finals);
    let(queries,rho)=query_schedule(&mut p,&finals,&[0;24]).unwrap();
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();
    let records:Vec<u8>=pts.iter().zip(&queries).flat_map(|(p,i)|{
        let r=f::record(p.x,2);if (*i as usize)<S{changed(r)}else{r}
    }).collect();
    let fa=f::frontier(a,&queries);let fb=f::frontier(b,&queries);
    let stub=f::body(&v,a,b,&records,(&fa,&fb));let w=parse(&stub).unwrap();
    let(values,xs)=opened_values(&w,&p,&queries,alpha,hash).unwrap();
    let mut residuals=0;
    for i in 0..Q{let truth=corelib::v6_onefold::evaluate_final256_coefficients(&finals,xs[i]).unwrap();
        if queries[i] as usize>=S{assert_eq!(truth,values[i]);}
        if truth!=values[i]{residuals+=1;}
    }
    let inc=inject(&mut weights,&mut claim,&values,&xs,rho).unwrap();p.t.absorb(label::PROFILE,&bytes(&[inc]));
    for r in 1..4{
        f::save_round(&mut v,r,polynomial_for_extension(&finals,&weights));
        let poly=compact(&v[417+r*6..423+r*6],claim);absorb_round(&mut p.t,r,&poly);
        let a=sample(&mut p.t,false).unwrap();claim=evaluate(&poly,a);
        weights.fold_deferred_relation_arity4(a);finals=primal(&finals,a);
    }
    (f::body(&v,a,b,&records,(&fa,&fb)),queries.iter().filter(|i|**i<(S as u32)).count(),residuals)
}
pub fn run(){
    let start=std::time::Instant::now();let(a,_)=f::trees(2);let b=c2tree();
    let(mut accepted,mut miss,mut hit_accepted,mut max_body)=(0,0,0,0);
    for seed in 1..=32{
        let(body,hits,residuals)=build(seed,&a,&b,K::ZERO);max_body=max_body.max(body.len());assert!(body.len()<=40282);
        let w=parse(&body).unwrap();let(p,weights,c,_)=row::prepare(row::semantic(&w,seed,true).unwrap(),&w,true).unwrap();
        let result=row::relation(&w,p,weights,c);
        if hits==0{miss+=1;assert_eq!(result,Ok(()));}
        if result.is_ok(){accepted+=1;if hits>0{hit_accepted+=1;}}
        println!("seed={seed} changed_queries={hits} nonzero_folded_residuals={residuals} accepted={}",result.is_ok());
    }
    for seed in 1..=4{let(body,_,_)=build(seed,&a,&b,K::ONE);let w=parse(&body).unwrap();
        let(p,weights,c,_)=row::prepare(row::semantic(&w,seed,true).unwrap(),&w,true).unwrap();
        println!("false_D_row_control seed={seed} accepted={}",row::relation(&w,p,weights,c).is_ok());
    }
    println!("SUMMARY fixed_seeds=32 accepted={accepted} missed_all={miss} hit_accepted={hit_accepted} max_body={max_body} wall_seconds={}",start.elapsed().as_secs_f64());
    println!("SCOPE source-shaped repaired row/image relation suffix with honest T2 codeword claims; semantic prefix opaque; not a complete payment proof. No seed search/retries.");
}
