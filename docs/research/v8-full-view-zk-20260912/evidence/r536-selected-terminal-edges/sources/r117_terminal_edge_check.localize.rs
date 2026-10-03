//! Isolated terminal differential. No parser, transcript, fixture, or verifier change.
//! Source helpers are imported by path from the frozen R117 root.
extern crate aspis_core as corelib;
extern crate aspis_statement;
#[derive(Debug,PartialEq)] enum Error { Shape, Domain }
use corelib::field::{CM31,M31,QM31 as K,P};
use corelib::sumcheck::WeightAccumulator;
#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_tensor_prefix; mod r17_compact_prepare; mod r18_compact_g;
mod r20_sparse_whole; mod r20_private_dot_adapter; mod r17_owned_weights;
mod r17_weighted_groups; mod r19_channel_ordinary; mod r17_structured_g; use r17_structured_g as structured_g;
mod r18_sparse_coded_g; mod r17_mask_workspace; mod r17_opening_weights;
#[path="r17_owned_primal.rs"] mod owned_primal;
#[path="r116_query.rs"] mod query;

// Exact current r17_host_relation.rs:313-321, retained locally only because
// that helper is private to the verifier module.
fn fold_dense(v:&[K],a:K)->Vec<K>{
    v.chunks_exact(4).map(|v|v[0].add(a.mul(v[3].add(a.mul(v[2].add(a.mul(v[1])))))).half().half()).collect()
}
// Exact relation_callback.rs:103-105.
fn image_terminal(t:K,b:K,c:K,a:[K;4])->K{
    a[1].mul(a[2]).mul(a[3]).mul(t.mul(a[0]).add(t.square().mul(b.mul(a[0].square()).sub(c.mul(a[0].square().mul(a[0])))))).mul_m31(M31(8388608))
}

#[derive(Clone)]
struct CurrentPrepared { z:[K;10], kappa:K, tau:K, abc:[K;3], coins:Vec<K> }

fn optimized_components(p:&CurrentPrepared, alpha:[K;4], beta:K, rho:K,
    values:&[K], xs:&[M31], final256:Vec<K>)->(K,K,K) {
    // Lines 489-513 of current verify_cached, factored without transcript work.
    let finals: [K;4]=[alpha[1],alpha[2],alpha[3]].into_iter()
        .fold(final256,|v,a|owned_primal::fold(v,a)).try_into().unwrap();
    let audit=core::array::from_fn(|i|if i<10 {p.z[i]}else{p.kappa});
    let kernel=r17_weighted_groups::Kernel::new(p.abc,alpha);
    let mut workspace=vec![K::ZERO;531];
    let ordinary_sparse=r19_channel_ordinary::r106_terminal(&audit,p.abc,alpha,beta,&finals,&mut workspace,&kernel,&p.coins);
    let mut q=query::Query::new(); let mut ignored_claim=K::ZERO;
    q.inject(&mut ignored_claim,values,xs,rho).unwrap();
    let query=q.terminal([alpha[1],alpha[2],alpha[3]],finals);
    let image_scale=K::ONE.sub(beta).add(beta.mul(p.tau.square()));
    (ordinary_sparse,query,image_scale.mul(image_terminal(p.tau,p.abc[1],p.abc[2],alpha)).mul(finals[3]))
}

fn dense_folded_components(p:&CurrentPrepared, alpha:[K;4], beta:K, rho:K,xs:&[M31])->([K;4],[K;4]) {
    let r=r17_opening_weights::quotient_weights(&p.z,p.kappa,p.abc,p.tau,false);
    let g=r17_opening_weights::quotient_weights(&p.z,p.kappa,p.abc,p.tau,true);
    let mut ordinary=fold_dense(&(0..1024).map(|i|r.weight_at(i).add(beta.mul(g.weight_at(i).sub(r.weight_at(i))))).collect::<Vec<_>>(),alpha[0]);
    let mut query=vec![K::ZERO;256];
    let mut power=rho;
    for &x in xs {
        for j in 0..256 { let mut unit=vec![K::ZERO;256]; unit[j]=K::ONE;
            query[j]=query[j].add(power.mul(corelib::v6_onefold::evaluate_final256_coefficients(&unit,x).unwrap())); }
        power=power.mul(rho);
    }
    for a in &alpha[1..] { ordinary=fold_dense(&ordinary,*a); query=fold_dense(&query,*a); }
    let mut ordinary:[K;4]=ordinary.try_into().unwrap();
    (ordinary,query.try_into().unwrap())
}

fn check_case(p:CurrentPrepared,alpha:[K;4],beta:K,rho:K,values:Vec<K>,xs:Vec<M31>,dense_ordinary:[K;4],dense_query:[K;4],final256:Vec<K>){
    let finals:[K;4]=[alpha[1],alpha[2],alpha[3]].into_iter().fold(final256.clone(),|v,a|owned_primal::fold(v,a)).try_into().unwrap();
    let (ordinary_sparse,query_terminal,image)=optimized_components(&p,alpha,beta,rho,&values,&xs,final256);
    let dense_ordinary=corelib::field::qm31_sum_products4(dense_ordinary,finals);
    let dense_query=corelib::field::qm31_sum_products4(dense_query,finals);
    assert_eq!(ordinary_sparse.add(image),dense_ordinary,"ordinary/image component");
    assert_eq!(query_terminal,dense_query,"query component");
    assert_eq!(ordinary_sparse.add(image).add(query_terminal),dense_ordinary.add(dense_query),"composed terminal");
}

fn sample(state:&mut u64)->K { let mut m=||{*state^=*state<<13;*state^=*state>>7;*state^=*state<<17;M31((*state%u64::from(P))as u32)}; K{c0:CM31::new(m(),m()),c1:CM31::new(m(),m())} }
fn nonzero(state:&mut u64)->K { loop {let k=sample(state);if k!=K::ZERO{return k;}} }
fn final_cases(state:&mut u64)->Vec<Vec<K>> { let mut out=Vec::new(); for i in [0usize,1,2,3,127,255] {let mut v=vec![K::ZERO;256];v[i]=K::ONE;out.push(v);} out.push((0..256).map(|_|sample(state)).collect());out }
fn canonical(q:K)->bool { q.c0.a.0<P && q.c0.b.0<P && q.c1.a.0<P && q.c1.b.0<P }
fn first_difference(left:&[K],right:&[K])->Option<usize>{left.iter().zip(right).position(|(a,b)|a!=b)}
fn main(){
    let z=[K::ZERO;10];let alpha=[K::ZERO;4];let beta=K::ZERO;let kappa=K::ONE;let tau=K::ONE;
    let o0=corelib::circle::secure_ood_circle_point_from_parameter(K{c0:CM31::new(M31(17),M31(29)),c1:CM31::new(M31(43),M31(71))}).unwrap();
    let o1=corelib::circle::secure_ood_circle_point_from_parameter(K{c0:CM31::new(M31(73),M31(97)),c1:CM31::new(M31(101),M31(131))}).unwrap();
    assert!(o0.x.c1!=CM31::ZERO || o0.y.c1!=CM31::ZERO);assert!(o1.x.c1!=CM31::ZERO || o1.y.c1!=CM31::ZERO);
    let abc=[o0.x.mul(o1.y).sub(o0.y.mul(o1.x)),o0.y.sub(o1.y),o1.x.sub(o0.x)];
    let final256={let mut v=vec![K::ZERO;256];v[0]=K::ONE;v};
    let finals:[K;4]=[alpha[1],alpha[2],alpha[3]].into_iter().fold(final256,|v,a|owned_primal::fold(v,a)).try_into().unwrap();
    assert!(z.into_iter().chain(alpha).chain(abc).chain(finals).all(canonical));
    let audit=core::array::from_fn(|i|if i<10 {z[i]}else{kappa});
    let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
    let mut coins=vec![K::ZERO;271];r18_sparse_coded_g::coin_weights_into(&z,&mut coins);assert!(coins.iter().copied().all(canonical));
    let original=r17_opening_weights::original_weights(&z,kappa,false);
    let reference=r17_opening_weights::original_weights_reference(&z,kappa,false);
    println!("ORIGINAL_WEIGHTS first_difference={:?}",first_difference(&original,&reference));assert_eq!(original,reference,"original weights");
    let mut workspace=vec![K::ZERO;531];
    let r106=r19_channel_ordinary::r106_terminal(&audit,abc,alpha,beta,&finals,&mut workspace,&kernel,&coins);
    let scalar=r19_channel_ordinary::terminal_scalar(&audit,abc,alpha,beta,&finals,&mut workspace,&kernel);
    println!("R106_SCALAR r106={:?} scalar={:?}",r106,scalar);assert_eq!(r106,scalar,"r106 versus terminal_scalar at beta zero");
    let base=r17_opening_weights::quotient_weights(&z,kappa,abc,tau,false);
    let mut accumulator=base.clone();
    for a in alpha {accumulator.fold_deferred_relation_arity4(a);}
    let accumulator_folded:[K;4]=core::array::from_fn(|i|accumulator.weight_at(i as u32));
    let mut copied=(0..1024).map(|i|base.weight_at(i)).collect::<Vec<_>>();
    for a in alpha {copied=fold_dense(&copied,a);}
    let copied:[K;4]=copied.try_into().unwrap();
    println!("FOLD first_difference={:?} accumulator={:?} copied={:?}",first_difference(&accumulator_folded,&copied),accumulator_folded,copied);assert_eq!(accumulator_folded,copied,"accumulator versus copied fold");
    let image=image_terminal(tau,abc[1],abc[2],alpha).mul(finals[3]);
    let scalar_image=scalar.add(image);let dense=corelib::field::qm31_sum_products4(accumulator_folded,finals);
    println!("TERMINAL scalar_image={:?} dense={:?}",scalar_image,dense);assert_eq!(scalar_image,dense,"terminal scalar plus image versus dense quotient dot");
    println!("R117_TERMINAL_SINGLE_CASE_OK");
}
