//! Exhaustive columns of the current-source sparse G core at algebraic witnesses.
//! No proof/transcript generation; the normalized witness is sampler-excluded.
extern crate aspis_core as corelib;
use corelib::field::{CM31,M31,QM31 as K};
#[path="r16_basis_transport.rs"] mod basis_transport;
#[path="r17_structured_g.rs"] mod structured_g;
mod r18_sparse_coded_g;mod r17_mask_workspace;mod r17_tensor_prefix;
mod r28_source_helpers;
use r28_source_helpers::chord;
fn block(x:&[K])->Vec<K>{(0..271).map(|i|if i%4==0{x[i].neg().sub(x[i+1])}else{x[i]}).collect()}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),2);
    let out=std::path::Path::new(&args[1]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    let map=basis_transport::transport();
    let columns:Vec<_>=(0..271).map(|i|{let n=r18_sparse_coded_g::slot(i);assert_eq!(n,128+3*i);let s=if n%4==0{1}else{n%4};3*(n/4-22)+s-1}).collect();
    assert!(columns.iter().all(|&c|c<699));let mut distinct=columns.clone();distinct.sort();distinct.dedup();assert_eq!(distinct.len(),271);
    let iota=K::from_cm31(CM31::new(M31::ZERO,M31::ONE));assert_eq!(iota.mul(iota),K::ONE.neg());
    let u=iota;let v=iota.neg();let normalized=[K::ONE.add(u.mul(v)),u.mul(v).sub(K::ONE),u.add(v).neg()];
    assert_eq!(normalized,[K::ONE.add(K::ONE),K::ZERO,K::ZERO]);
    assert_eq!(K::ONE.add(u.mul(u)),K::ZERO);assert_eq!(K::ONE.add(v.mul(v)),K::ZERO);
    let mut source_checks=0;let mut inverse_checks=0;let mut negative=0;
    for j in 0..271{
        let mut x=vec![K::ZERO;271];x[j]=K::ONE;let expected=block(&x);assert_eq!(block(&expected),x);inverse_checks+=271;
        let d=22+columns[j]/3;let k=1+columns[j]%3;
        let mut q=vec![K::ZERO;1024];q[4*d+k]=K::ONE;q[4*d]=K::ONE.neg();
        assert!(q[1021..].iter().all(|&v|v==K::ZERO));assert!(q.chunks_exact(4).all(|a|a.iter().fold(K::ZERO,|s,&v|s.add(v))==K::ZERO));
        for (abc,scale) in [([K::ONE,K::ZERO,K::ZERO],K::ONE),(normalized,K::ONE.add(K::ONE))]{
            let c=chord(&q,abc);let m=map.inverse(&c);assert_eq!(map.forward(&m),c);
            let coins=structured_g::mixed_coins(&m);
            for i in 0..271{assert_eq!(coins[i],scale.mul(expected[i]),"source minor row={i} column={j}");source_checks+=1;}
            let restored=block(&coins.iter().map(|&v|v.mul(scale.inv())).collect::<Vec<_>>());assert_eq!(restored,x);
        }
        // A missing partner coefficient or wrong diagonal sign must be detectable.
        if j%4==1{assert_ne!(expected[j-1],x[j-1].neg());negative+=1;}
        if j%4==0{assert_ne!(expected[j],x[j]);negative+=1;}
    }
    assert_eq!(negative,136);
    std::fs::write(out.join("summary.json"),format!("{{\"columns\":{:?},\"selected_columns\":271,\"pair_blocks\":68,\"singletons\":135,\"source_matrix_entries_checked\":{source_checks},\"inverse_coordinates_checked\":{inverse_checks},\"negative_controls\":{negative},\"normalized_chord\":[2,0,0],\"normalized_witness_sampler_excluded\":true,\"actual_transcript_generated\":false,\"all_source_prefixes_covered\":false,\"full_privacy\":false}}\n",columns)).unwrap();
    println!("R31_SPARSE_G_CORE source_entries={source_checks} inverse_coordinates={inverse_checks} negatives={negative} algebraic_only=true sampler_excluded=true full_privacy=false");
}
