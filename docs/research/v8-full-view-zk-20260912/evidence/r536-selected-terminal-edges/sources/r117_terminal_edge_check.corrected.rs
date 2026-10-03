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
    let image_scale=K::ONE.sub(beta).add(beta.mul(p.tau.square()));
    ordinary[3]=ordinary[3].add(image_scale.mul(image_terminal(p.tau,p.abc[1],p.abc[2],alpha)));
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
fn main(){
    let mut state=0x117ed9e21c34ab5u64;
    let z_cases=[[K::ZERO;10],[K::ONE;10],core::array::from_fn(|_|sample(&mut state))];
    let alpha_cases=[[K::ZERO;4],[K::ONE;4],[K::ZERO,K::ONE,K::ZERO,K::ONE],[K::ONE,K::ZERO,K::ONE,K::ZERO],core::array::from_fn(|_|sample(&mut state))];
    let beta_cases=[K::ZERO,K::ONE,sample(&mut state)];
    let o0=corelib::circle::secure_ood_circle_point_from_parameter(K{c0:CM31::new(M31(17),M31(29)),c1:CM31::new(M31(43),M31(71))}).unwrap();
    let o1=corelib::circle::secure_ood_circle_point_from_parameter(K{c0:CM31::new(M31(73),M31(97)),c1:CM31::new(M31(101),M31(131))}).unwrap();
    assert!(o0.x.c1!=CM31::ZERO || o0.y.c1!=CM31::ZERO);assert!(o1.x.c1!=CM31::ZERO || o1.y.c1!=CM31::ZERO);
    let ood_abc=[o0.x.mul(o1.y).sub(o0.y.mul(o1.x)),o0.y.sub(o1.y),o1.x.sub(o0.x)];
    for z in z_cases.into_iter(){for &alpha in &alpha_cases {for &beta in &beta_cases {for scalar_case in 0..2 {
        let (kappa,tau)=if scalar_case==0 {(K::ONE,K::ONE)}else{(nonzero(&mut state),nonzero(&mut state))};
        assert!(kappa!=K::ZERO && tau!=K::ZERO);
        let mut coins=vec![K::ZERO;271];r18_sparse_coded_g::coin_weights_into(&z,&mut coins);
        let p=CurrentPrepared{z,kappa,tau,abc:ood_abc,coins};
        let values:Vec<K>=(0..22).map(|_|sample(&mut state)).collect();let xs:Vec<M31>=(0..22).map(|_|{let v=sample(&mut state);v.c0.a}).collect();let rho=nonzero(&mut state);assert!(rho!=K::ZERO);
        let (dense_ordinary,dense_query)=dense_folded_components(&p,alpha,beta,rho,&xs);
        for final256 in final_cases(&mut state){check_case(p.clone(),alpha,beta,rho,values.clone(),xs.clone(),dense_ordinary,dense_query,final256);}
    }}}}
}
