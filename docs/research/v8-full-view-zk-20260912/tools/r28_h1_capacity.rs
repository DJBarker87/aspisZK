//! Fixed, genuine source-prefix H1 first-relation capacity certificate.
//! No challenge substitution, witness generation, protocol change or privacy claim.
extern crate aspis_core as corelib;
#[path="../../../../crates/aspis-prover/src/state_only_hiding.rs"] mod state_only_hiding;
#[path="../../../../crates/aspis-prover/src/state_only_zerocheck.rs"] mod state_only_zerocheck;
use corelib::field::{CM31, M31, QM31 as K};
use corelib::sumcheck::{WeightAccumulator, polynomial_for_extension, evaluate};
#[path="r16_basis_transport.rs"] mod basis_transport;
#[path="r17_structured_g.rs"] mod structured_g;
mod r18_sparse_coded_g;
mod r17_mask_workspace;
mod r17_tensor_prefix;
#[path="r17_opening_weights.rs"] mod opening_weights;
mod r28_source_helpers;
use r28_source_helpers::{chord,dot,eval_weights,qvector};

fn primal(q:&[K], a:K)->Vec<K> {
    q.chunks_exact(4).map(|v|v[0].add(a.mul(v[1].add(a.mul(v[2].add(a.mul(v[3]))))))).collect()
}
fn encoded(v:&[K])->Vec<u8> {
    let mut b=vec![0;16*v.len()];for(i,x)in v.iter().enumerate(){x.write_le_bytes(&mut b[16*i..16*i+16]);}b
}

fn main() {
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);
    let input=std::fs::read(&args[1]).unwrap();assert_eq!(input.len(),21*16+22*4);
    let fields:Vec<_>=input[..336].chunks_exact(16).map(|b|K::from_le_bytes(b).unwrap()).collect();
    let z:[K;10]=fields[..10].try_into().unwrap();let kappa=fields[10];let tau=fields[11];let alpha=fields[12];
    let [sx,sy,zx,zy]:[K;4]=fields[13..17].try_into().unwrap();
    let abc=[sx.mul(zy).sub(sy.mul(zx)),sy.sub(zy),zx.sub(sx)];
    let queries:Vec<_>=input[336..].chunks_exact(4).map(|b|u32::from_le_bytes(b.try_into().unwrap())).collect();
    let out=std::path::Path::new(&args[2]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    let map=basis_transport::transport();
    let active:Vec<_>=(0..1024).filter(|&r|!map.inactive[r]).collect();assert_eq!(active.len(),214);
    let rawpoints=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();
    let raw:Vec<_>=rawpoints.iter().flat_map(|p|[(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)])
        .map(|(x,y)|eval_weights(K::from_cm31(CM31::from_m31(x)),K::from_cm31(CM31::from_m31(y)))).collect();
    let point:Vec<Vec<K>>=corelib::v6_transcript::v6_statement_points(&z).iter().map(|z|{
        let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,z.to_vec()).unwrap();
        (0..1024).map(|j|w.weight_at(j)).collect()
    }).collect();
    let wr=opening_weights::quotient_weights(&z,kappa,abc,tau,false);
    let sent=[0,1,2,3,5,6];
    // With c4=-c0, this is the exact evaluation covector on sent coefficients.
    let e=[K::ONE.sub(alpha.pow(4)),alpha,alpha.square(),alpha.pow(3),alpha.pow(5),alpha.pow(6)];
    let pivot=e.iter().position(|&x|x!=K::ZERO).unwrap();
    let free:Vec<_>=(0..6).filter(|&i|i!=pivot).collect();
    let targets:Vec<[K;7]>=free.iter().map(|&i|{
        let mut p=[K::ZERO;7];p[sent[i]]=K::ONE;p[sent[pivot]]=e[i].neg().mul(e[pivot].inv());p[4]=p[0].neg();
        assert_eq!(evaluate(&p,alpha),K::ZERO);assert_eq!(p[0].add(p[4]),K::ZERO);p
    }).collect();
    let start=std::time::Instant::now();eprintln!("R28 phase=matrix_construction rows=568 columns=1022 rhs=5");
    let mut matrix=vec![vec![K::ZERO;1022];568];
    for j in 0..1022 {
        let mut unit=vec![K::ZERO;1022];unit[j]=K::ONE;
        let q=qvector(&unit,abc);let c=chord(&q,abc);let m=map.inverse(&c);
        for(i,&r)in active.iter().enumerate(){matrix[i][j]=m[r];}
        matrix[214][j]=(0..1024).filter(|&r|map.inactive[r]).fold(K::ZERO,|s,r|s.add(m[r]));
        for i in 0..88 {matrix[215+i][j]=dot(&raw[i],&c);}
        for i in 0..3 {matrix[303+i][j]=dot(&point[i],&m);}
        let f=primal(&q,alpha);for i in 0..256 {matrix[306+i][j]=f[i];}
        let p=polynomial_for_extension(&q,&wr);for i in 0..6 {matrix[562+i][j]=p[sent[i]];}
    }
    eprintln!("R28 matrix_seconds={} phase=single_incremental_elimination",start.elapsed().as_secs_f64());
    // Incremental row echelon preserves the baseline/new-row rank boundary.
    // The five right-hand sides yield an explicit right inverse, checked below
    // against the original matrix AND the original source functions.
    let mut echelon:Vec<Vec<K>>=Vec::new();let mut pivots:Vec<usize>=Vec::new();let mut baseline=0;
    for(i,original)in matrix.iter().enumerate(){
        let mut row=original.clone();for target in &targets{row.push(if i<562{K::ZERO}else{target[sent[i-562]]});}
        for(k,&p)in pivots.iter().enumerate(){let f=row[p];if f!=K::ZERO{for j in 0..1027{row[j]=row[j].sub(f.mul(echelon[k][j]));}}}
        if let Some(p)=(0..1022).find(|&j|row[j]!=K::ZERO){let inv=row[p].inv();for v in &mut row{*v=v.mul(inv);}pivots.push(p);echelon.push(row);}
        else {assert!(row[1022..].iter().all(|&v|v==K::ZERO),"incompatible target row {i}");}
        if i==561 {baseline=pivots.len();eprintln!("R28 baseline_rank={baseline}");}
    }
    assert_eq!(baseline,540);assert_eq!(pivots.len(),545);
    let mut certificate=Vec::new();let mut checked_rows=0;
    for t in 0..5 {
        let mut x=vec![K::ZERO;1022];
        for k in (0..pivots.len()).rev(){let p=pivots[k];assert_eq!(x[p],K::ZERO);x[p]=echelon[k][1022+t].sub(dot(&echelon[k][..1022],&x));}
        for i in 0..568 {assert_eq!(dot(&matrix[i],&x),if i<562{K::ZERO}else{targets[t][sent[i-562]]},"target {t} row {i}");checked_rows+=1;}
        let q=qvector(&x,abc);let c=chord(&q,abc);let pad=map.inverse(&c);
        let mut applied=vec![K::ZERO;1024];
        state_only_hiding::apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied,&pad).unwrap();assert_eq!(applied,pad);
        assert!(active.iter().all(|&r|pad[r]==K::ZERO));
        for w in &raw {assert_eq!(dot(w,&c),K::ZERO);}
        for w in &point {assert_eq!(dot(w,&pad),K::ZERO);}
        assert!(primal(&q,alpha).iter().all(|&v|v==K::ZERO));
        for(x,y)in [(sx,sy),(zx,zy)]{assert_eq!(dot(&eval_weights(x,y),&c),K::ZERO);}
        assert_eq!(polynomial_for_extension(&q,&wr),targets[t]);
        let mut bad=x.clone();bad[0]=bad[0].add(K::ONE);
        assert!(matrix.iter().enumerate().any(|(i,row)|dot(row,&bad)!=(if i<562{K::ZERO}else{targets[t][sent[i-562]]})),"corrupt certificate rejected");
        certificate.extend(encoded(&x));
    }
    std::fs::write(out.join("right-inverse.bin"),&certificate).unwrap();
    std::fs::write(out.join("targets.bin"),encoded(&targets.concat())).unwrap();
    println!("R28_H1_CAPACITY baseline_rank={baseline} augmented_rank={} kernel_image_dimension=5 original_rows_checked={checked_rows} source_polynomial_checks=5 h1_mask_api_checks=5 raw_zero_checks=440 point_zero_checks=15 ood_zero_checks=10 final_zero_checks=1280 corrupt_certificates_rejected=5 source_beta_changed=false full_privacy=false seconds={}",pivots.len(),start.elapsed().as_secs_f64());
}
