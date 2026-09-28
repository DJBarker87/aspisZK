//! Whole compatible target space at a pinned prefix, not a universal rank claim.
extern crate aspis_core as corelib;
use corelib::field::{CM31,M31,QM31 as K};
use corelib::sumcheck::{WeightAccumulator,polynomial_for_extension,evaluate};
#[path="r16_basis_transport.rs"] mod basis_transport;
#[path="r17_structured_g.rs"] mod structured_g;
mod r18_sparse_coded_g;
mod r17_mask_workspace;
mod r17_tensor_prefix;
#[path="r17_opening_weights.rs"] mod opening_weights;
mod r28_source_helpers;
use r28_source_helpers::{chord,dot,eval_weights,qvector};
use sha2::{Digest,Sha256};

fn primal(q:&[K],a:K)->Vec<K>{q.chunks_exact(4).map(|v|v[0].add(a.mul(v[1].add(a.mul(v[2].add(a.mul(v[3]))))))).collect()}
const ROWS:usize=633;const COLS:usize=1022;const TARGETS:usize=276;
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);
    let b=std::fs::read(&args[1]).unwrap();assert_eq!(b.len(),424);
    let f:Vec<_>=b[..336].chunks_exact(16).map(|v|K::from_le_bytes(v).unwrap()).collect();
    let z:[K;10]=f[..10].try_into().unwrap();let k=f[10];let tau=f[11];let alpha=f[12];
    let [sx,sy,zx,zy]:[K;4]=f[13..17].try_into().unwrap();let abc=[sx.mul(zy).sub(sy.mul(zx)),sy.sub(zy),zx.sub(sx)];
    let queries:Vec<_>=b[336..].chunks_exact(4).map(|b|u32::from_le_bytes(b.try_into().unwrap())).collect();
    let out=std::path::Path::new(&args[2]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    let map=basis_transport::transport();
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();
    let raw:Vec<_>=pts.iter().flat_map(|p|[(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)])
        .map(|(x,y)|eval_weights(K::from_cm31(CM31::from_m31(x)),K::from_cm31(CM31::from_m31(y)))).collect();
    let mut point:Vec<Vec<K>>=corelib::v6_transcript::v6_statement_points(&z).iter().map(|z|{
        let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,z.to_vec()).unwrap();(0..1024).map(|j|w.weight_at(j)).collect()
    }).collect();point[0]=structured_g::mask_weights(&z);
    let rw=opening_weights::quotient_weights(&z,k,abc,tau,false);
    let gw=opening_weights::quotient_weights(&z,k,abc,tau,true);
    let l:Vec<_>=(0..271).map(|i|{let mut u=[K::ZERO;271];u[i]=K::ONE;structured_g::mask_eval(&u,&z)}).collect();
    assert_ne!(l[0],K::ZERO);let inv=l[0].inv();
    let mut targets=vec![vec![K::ZERO;ROWS];TARGETS];
    for i in 1..271 {targets[i-1][i]=K::ONE;targets[i-1][0]=l[i].neg().mul(inv);}
    for i in 1..7 {targets[270+i-1][619+i]=K::ONE;targets[270+i-1][619]=alpha.pow(i as u64).neg();}
    let start=std::time::Instant::now();eprintln!("R29 phase=G_matrix rows={ROWS} columns={COLS} rhs={TARGETS}");
    let mut matrix=vec![vec![K::ZERO;COLS];ROWS];
    for j in 0..COLS {
        let mut unit=vec![K::ZERO;COLS];unit[j]=K::ONE;let q=qvector(&unit,abc);let c=chord(&q,abc);let m=map.inverse(&c);
        let coins=structured_g::mixed_coins(&m);for i in 0..271{matrix[i][j]=coins[i];}
        for i in 0..88{matrix[271+i][j]=dot(&raw[i],&c);}
        for i in 0..3{matrix[359+i][j]=dot(&point[i],&m);}
        let f=primal(&q,alpha);for i in 0..256{matrix[362+i][j]=f[i];}
        matrix[618][j]=(0..1024).filter(|&r|map.inactive[r]).fold(K::ZERO,|s,r|s.add(m[r]));
        let pr=polynomial_for_extension(&q,&rw);let pg=polynomial_for_extension(&q,&gw);
        for i in 0..7{matrix[619+i][j]=pr[i];matrix[626+i][j]=pg[i];}
    }
    eprintln!("R29 matrix_seconds={} phase=single_multi_rhs_elimination",start.elapsed().as_secs_f64());
    let mut rows:Vec<Vec<K>>=Vec::new();let mut pivots:Vec<usize>=Vec::new();
    for(i,original)in matrix.iter().enumerate(){
        let mut row=original.clone();row.extend(targets.iter().map(|t|t[i]));
        for(k,&p)in pivots.iter().enumerate(){let f=row[p];if f!=K::ZERO{for j in 0..COLS+TARGETS{row[j]=row[j].sub(f.mul(rows[k][j]));}}}
        if let Some(p)=(0..COLS).find(|&j|row[j]!=K::ZERO){let inv=row[p].inv();for v in &mut row{*v=v.mul(inv);}pivots.push(p);rows.push(row);}
        else{assert!(row[COLS..].iter().all(|&v|v==K::ZERO),"compatible target family at row {i}");}
    }
    assert_eq!(pivots.len(),607);eprintln!("R29 rank=607 phase=all_original_rows_and_source_rechecks");
    let mut cert=Vec::new();let mut bad_count=0;
    for t in 0..TARGETS {
        let mut x=vec![K::ZERO;COLS];
        for n in(0..pivots.len()).rev(){let p=pivots[n];assert_eq!(x[p],K::ZERO);x[p]=rows[n][COLS+t].sub(dot(&rows[n][..COLS],&x));}
        for i in 0..ROWS{assert_eq!(dot(&matrix[i],&x),targets[t][i],"target {t} original row {i}");}
        let q=qvector(&x,abc);let c=chord(&q,abc);let m=map.inverse(&c);
        assert_eq!(structured_g::mixed_coins(&m).as_slice(),&targets[t][..271]);
        assert_eq!(structured_g::mask_eval(&structured_g::mixed_coins(&m),&z),K::ZERO);
        for w in &raw{assert_eq!(dot(w,&c),K::ZERO);}
        for w in &point{assert_eq!(dot(w,&m),K::ZERO);}
        for(x,y)in[(sx,sy),(zx,zy)]{assert_eq!(dot(&eval_weights(x,y),&c),K::ZERO);}
        assert_eq!((0..1024).filter(|&r|map.inactive[r]).fold(K::ZERO,|s,r|s.add(m[r])),K::ZERO);
        assert!(primal(&q,alpha).iter().all(|&v|v==K::ZERO));
        let pr=polynomial_for_extension(&q,&rw);assert_eq!(pr.as_slice(),&targets[t][619..626]);assert_eq!(evaluate(&pr,alpha),K::ZERO);
        assert_eq!(polynomial_for_extension(&q,&gw),[K::ZERO;7]);
        let mut bad=x.clone();bad[0]=bad[0].add(K::ONE);assert!(matrix.iter().enumerate().any(|(i,row)|dot(row,&bad)!=targets[t][i]));bad_count+=1;
        for v in x{let mut b=[0;16];v.write_le_bytes(&mut b);cert.extend_from_slice(&b);}
    }
    // Keep the complete public right inverse on the build host. The repository
    // receipt commits its hash, not a claim of kernel replay of this binary.
    std::fs::write(out.join("right-inverse.bin"),&cert).unwrap();
    let hash=Sha256::digest(&cert);let hex:String=hash.iter().map(|b|format!("{b:02x}")).collect();
    std::fs::write(out.join("certificate.json"),format!("{{\"sha256\":\"{hex}\",\"bytes\":{},\"rank\":607,\"target_directions\":276,\"original_equations_checked\":{},\"beta_in_matrix\":false,\"universal_source_theorem\":false}}\n",cert.len(),ROWS*TARGETS)).unwrap();
    println!("R29_G_CAPACITY rank=607 target_basis=276 original_equations={} source_rechecks=276 negative_controls={bad_count} beta_in_matrix=false source_prefix_substituted=false full_privacy=false seconds={}",ROWS*TARGETS,start.elapsed().as_secs_f64());
}
