//! Current-source high-coordinate section of the balanced raw/final kernel.
//! Reuses the R17 polynomial-kernel construction; no transcript substitution.
extern crate aspis_core as corelib;
use corelib::field::{CM31,M31,QM31 as K};
use corelib::sumcheck::{WeightAccumulator,polynomial_for_extension};
#[path="../../../../crates/aspis-prover/src/state_only_hiding.rs"] mod state_only_hiding;
#[path="../../../../crates/aspis-prover/src/state_only_zerocheck.rs"] mod state_only_zerocheck;
#[path="r16_basis_transport.rs"] mod basis_transport;
#[path="r17_structured_g.rs"] mod structured_g;
mod r18_sparse_coded_g;mod r17_mask_workspace;mod r17_tensor_prefix;
#[path="r17_opening_weights.rs"] mod opening_weights;
mod r28_source_helpers;
use r28_source_helpers::{chord,dot,eval_weights,times_x};
fn primal(q:&[K],a:K)->Vec<K>{q.chunks_exact(4).map(|v|v[0].add(a.mul(v[1].add(a.mul(v[2].add(a.mul(v[3]))))))).collect()}
fn channel(v:&[K],slot:usize,a:K)->Vec<K>{
    let mut q=vec![K::ZERO;1024];let scale=a.pow(slot as u64);
    for(i,&x)in v.iter().enumerate(){q[4*i+slot]=x;q[4*i]=scale.mul(x).neg();}q
}
fn rank_steps(matrix:&[Vec<K>],core:usize)->(usize,usize,Vec<usize>){
    let mut rows:Vec<Vec<K>>=Vec::new();let mut pivots:Vec<usize>=Vec::new();let mut first=0;
    for(i,original)in matrix.iter().enumerate(){let mut row=original.clone();
        for(k,&p)in pivots.iter().enumerate(){let f=row[p];if f!=K::ZERO{for j in 0..699{row[j]=row[j].sub(f.mul(rows[k][j]));}}}
        if let Some(p)=(0..699).find(|&j|row[j]!=K::ZERO){let inv=row[p].inv();for x in &mut row{*x=x.mul(inv);}rows.push(row);pivots.push(p);}
        if i+1==core{first=pivots.len();}
    }(first,pivots.len(),pivots)
}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);
    let bytes=std::fs::read(&args[1]).unwrap();assert_eq!(bytes.len(),424);
    let f:Vec<_>=bytes[..336].chunks_exact(16).map(|b|K::from_le_bytes(b).unwrap()).collect();
    let z:[K;10]=f[..10].try_into().unwrap();let k=f[10];let tau=f[11];let alpha=f[12];
    let [sx,sy,zx,zy]:[K;4]=f[13..17].try_into().unwrap();let abc=[sx.mul(zy).sub(sy.mul(zx)),sy.sub(zy),zx.sub(sx)];
    let queries:Vec<_>=bytes[336..].chunks_exact(4).map(|b|u32::from_le_bytes(b.try_into().unwrap())).collect();
    let out=std::path::Path::new(&args[2]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    let map=basis_transport::transport();let active:Vec<_>=(0..1024).filter(|&r|!map.inactive[r]).collect();assert_eq!(active.len(),214);
    let active_code:Vec<_>=(0..1024).filter(|&i|!map.inactive[map.order[i]]).collect();
    let start=std::time::Instant::now();eprintln!("R30 phase=complete_low_support_basis active_min={} G_min=128",active_code[0]);
    let mut max_support=0;
    for j in 0..88{for axis in 0..3{
        let mut q=vec![K::ZERO;1024];q[j]=K::ONE;let mut a=[K::ZERO;3];a[axis]=K::ONE;let c=chord(&q,a);
        if let Some(last)=c.iter().rposition(|&x|x!=K::ZERO){max_support=max_support.max(last);}
        let m=map.inverse(&c);assert!(active.iter().all(|&r|m[r]==K::ZERO));
        assert_eq!(structured_g::mixed_coins(&m),[K::ZERO;271]);
        let mut applied=vec![K::ZERO;1024];state_only_hiding::apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied,&m).unwrap();assert_eq!(applied,m);
    }}
    assert_eq!(max_support,90);assert!(active_code[0]>90);
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();
    let roots:Vec<_>=pts.iter().map(|p|p.x.mul(p.x).double().sub(M31::ONE)).collect();
    let mut distinct=roots.clone();distinct.sort_by_key(|v|v.0);distinct.dedup();assert_eq!(distinct.len(),22);
    let raw:Vec<_>=pts.iter().flat_map(|p|[(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)])
        .map(|(x,y)|eval_weights(K::from_cm31(CM31::from_m31(x)),K::from_cm31(CM31::from_m31(y)))).collect();
    let mut factor=vec![K::ONE];for &r in &roots{let mut next=times_x(&factor);for i in 0..factor.len(){next[i]=next[i].sub(factor[i].mul_m31(r));}factor=next;}
    // P*t^j is upper triangular in the source natural coefficient basis.
    let mut multiples=Vec::new();for d in 22..255{assert_eq!(factor.len(),d+1);assert_ne!(factor[d],K::ZERO);multiples.push(factor.clone());factor=times_x(&factor);}
    let point:Vec<Vec<K>>=corelib::v6_transcript::v6_statement_points(&z).iter().map(|z|{let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,z.to_vec()).unwrap();(0..1024).map(|i|w.weight_at(i)).collect()}).collect();
    let rw=opening_weights::quotient_weights(&z,k,abc,tau,false);let gw=opening_weights::quotient_weights(&z,k,abc,tau,true);
    let mut hm=vec![vec![];224];let mut gm=vec![vec![];288];let mut changed_residual=false;
    eprintln!("R30 phase=normalized_kernel_section columns=699");
    for d in 22..255{
        let mut remainder=vec![K::ZERO;256];remainder[d]=K::ONE;
        for h in(22..=d).rev(){let m=&multiples[h-22];let scale=remainder[h].mul(m[h].inv());for j in 0..=h{remainder[j]=remainder[j].sub(scale.mul(m[j]));}}
        assert!(remainder[22..].iter().all(|&v|v==K::ZERO));
        let mut v:Vec<_>=remainder.iter().map(|v|v.neg()).collect();v[d]=K::ONE;
        for &r in &roots{assert_eq!(corelib::v6_onefold::evaluate_final256_coefficients(&v,r).unwrap(),K::ZERO);}
        for slot in 1..4{
            let q=channel(&v,slot,alpha);let mut unit=vec![K::ZERO;256];unit[d]=K::ONE;let direct=channel(&unit,slot,alpha);
            assert_eq!(&q[88..],&direct[88..]);assert!(q[1021..].iter().all(|&v|v==K::ZERO));assert!(primal(&q,alpha).iter().all(|&v|v==K::ZERO));
            let c=chord(&q,abc);let m=map.inverse(&c);let md=map.inverse(&chord(&direct,abc));
            for(i,&r)in active.iter().enumerate(){assert_eq!(m[r],md[r],"H direct core");hm[i].push(m[r]);}
            let coins=structured_g::mixed_coins(&m);assert_eq!(coins,structured_g::mixed_coins(&md),"G direct core");
            for i in 0..271{gm[i].push(coins[i]);}
            assert_eq!((0..1024).filter(|&r|map.inactive[r]).fold(K::ZERO,|s,r|s.add(m[r])),K::ZERO);
            for w in &raw{assert_eq!(dot(w,&c),K::ZERO);}
            for(x,y)in[(sx,sy),(zx,zy)]{assert_eq!(dot(&eval_weights(x,y),&c),K::ZERO);}
            for i in 0..3{hm[214+i].push(dot(&point[i],&m));gm[271+i].push(if i==0{structured_g::mask_eval(&coins,&z)}else{dot(&point[i],&m)});}
            let pr=polynomial_for_extension(&q,&rw);let pg=polynomial_for_extension(&q,&gw);
            for i in 0..7{hm[217+i].push(pr[i]);gm[274+i].push(pr[i]);gm[281+i].push(pg[i]);}
            if dot(&point[0],&m)!=dot(&point[0],&md){changed_residual=true;}
        }
    }
    // Negative control: the low repair is NOT invisible to every observation.
    assert!(changed_residual,"ordinary point residual must not be dropped");
    eprintln!("R30 phase=core_then_residual_elimination");
    let(hcore,hrank,hp)=rank_steps(&hm,214);let(gcore,grank,gp)=rank_steps(&gm,271);
    assert_eq!((hcore,hrank,gcore,grank),(214,222,271,284));
    std::fs::write(out.join("summary.json"),format!("{{\"low_basis_checks\":264,\"low_support_max\":90,\"active_min\":{},\"kernel_columns\":699,\"H_core_rank\":214,\"H_residual_rows\":10,\"H_residual_rank\":8,\"G_core_rank\":271,\"G_residual_rows\":17,\"G_residual_rank\":13,\"H_pivot_columns\":{:?},\"G_pivot_columns\":{:?},\"point_negative_control\":true,\"universal_rank_proved\":false,\"full_privacy\":false}}\n",active_code[0],hp,gp)).unwrap();
    println!("R30_KERNEL low_basis=264 columns=699 core_coordinate_equalities={} raw_zero_checks={} H_core={hcore} H_residual={} G_core={gcore} G_residual={} point_negative=true source_prefix_substituted=false full_privacy=false seconds={}",699*(214+271),699*88,hrank-hcore,grank-gcore,start.elapsed().as_secs_f64());
}
