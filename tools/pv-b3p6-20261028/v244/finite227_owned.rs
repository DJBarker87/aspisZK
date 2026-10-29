use aspis_core::field::{CM31,M31,QM31,P};
use aspis_core::state_only_prefix::r0::{Challenges,Error};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
fn q(n:u32)->QM31 {QM31{c0:CM31::new(M31(n%P),M31(n.wrapping_mul(17)%P)),c1:CM31::new(M31(n.wrapping_mul(31)%P),M31(n.wrapping_mul(47)%P))}}
fn main(){
 assert!(!cfg!(debug_assertions));
 let mut checks=0;let mut ok=0;let mut err=0;
 for withdrawal in [false,true]{
  let f=aspis_prover::r0_fixture::prepare(withdrawal);
  for seed in 0..16u32{
   let mut claims=core::array::from_fn(|r|core::array::from_fn(|c|q(seed*131+r as u32*29+c as u32)));
   let alpha=core::array::from_fn(|i|if seed<2 {if seed==0 {QM31::ZERO}else{QM31::ONE}}else{q(seed*71+i as u32)});
   let ch=Challenges{lambda:q(seed*7),chi:q(seed*11),theta:q(seed*13),zc:core::array::from_fn(|i|q(seed*19+i as u32)),mu:q(seed*23),eta:q(seed*29)};
   for rejected in [false,true]{
    let mut transition=*match f.public(){Public::Transfer(_,t)|Public::Withdrawal(_,t)=>t};
    if rejected{transition.candidate_afterstate.next_pair_index=transition.live_snapshot.next_pair_index;}
    let pub_=match f.public(){Public::Transfer(p,_)=>Public::Transfer(p,&transition),Public::Withdrawal(p,_)=>Public::Withdrawal(p,&transition)};
    let reference=match pub_{Public::Transfer(p,t)=>pv_b3p6_reference227::host_terminal::r0::Public::Transfer(p,t),Public::Withdrawal(p,t)=>pv_b3p6_reference227::host_terminal::r0::Public::Withdrawal(p,t)};
    let owned=match pub_{Public::Transfer(p,t)=>pv_b3p6_reference227::reference_terminal::r0::Public::Transfer(p,t),Public::Withdrawal(p,t)=>pv_b3p6_reference227::reference_terminal::r0::Public::Withdrawal(p,t)};
    let host=aspis_r1_cost_probe::host_public::terminal_qm31(pub_,&claims,&alpha,&ch);
    assert_eq!(host,pv_b3p6_reference227::reference_terminal::native227(owned,&claims,&alpha,&ch),"new owned reference seed={seed}, withdrawal={withdrawal}, rejected={rejected}");
    let copied=reference.terminal_qm31(&claims,&alpha,&ch);
    assert_eq!(host,copied,"host/copy seed={seed}, withdrawal={withdrawal}, rejected={rejected}");
    let statement=pub_.terminal_qm31(&claims,&alpha,&ch);
    assert_eq!(host,statement,"host/statement seed={seed}, withdrawal={withdrawal}, rejected={rejected}");
    match host{Ok(_)=>ok+=1,Err(Error::Public)=>err+=1,other=>panic!("unexpected result {other:?}")};
    // D claims at column28 are absent from the selected84-cell terminal view.
    claims[0][28]=q(234567);claims[1][28]=q(345678);claims[2][28]=q(456789);
    assert_eq!(host,aspis_r1_cost_probe::host_public::terminal_qm31(pub_,&claims,&alpha,&ch));
    assert_eq!(host,pv_b3p6_reference227::reference_terminal::native227(owned,&claims,&alpha,&ch),"D perturbation of new owned reference");
    checks+=1;
   }
  }
 }
 assert_eq!(ok,32);assert_eq!(err,32);
 println!("finite validation: {checks} same-input complete native Results across deployed host, owned byte-identical host, statement and iterator-free reference; ok={ok}, public_error={err}; D-column perturbations checked; no universal equality or row closure claimed");
}
