//! Current-source Schur residual after eliminating R31's fixed G minor.
//! Same accepted prefixes; no synthetic transcript or uniform-law claim.
extern crate aspis_core as corelib;
use corelib::field::{CM31,M31,QM31 as K};
use corelib::sumcheck::{WeightAccumulator,polynomial_for_extension,evaluate,boundary_sum};
#[path="r16_basis_transport.rs"] mod basis_transport;
#[path="r17_structured_g.rs"] mod structured_g;
mod r18_sparse_coded_g;mod r17_mask_workspace;mod r17_tensor_prefix;
#[path="r17_opening_weights.rs"] mod opening_weights;
mod r28_source_helpers;
use r28_source_helpers::{chord,dot,eval_weights,times_x};
use sha2::{Digest,Sha256};
const N:usize=699;const C:usize=271;const R:usize=17;const T:usize=276;
fn channel(v:&[K],slot:usize,a:K)->Vec<K>{let mut q=vec![K::ZERO;1024];let s=a.pow(slot as u64);for(i,&x)in v.iter().enumerate(){q[4*i+slot]=x;q[4*i]=s.mul(x).neg();}q}
fn primal(q:&[K],a:K)->Vec<K>{q.chunks_exact(4).map(|v|v[0].add(a.mul(v[1].add(a.mul(v[2].add(a.mul(v[3]))))))).collect()}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);
    let bytes=std::fs::read(&args[1]).unwrap();assert_eq!(bytes.len(),424);
    let f:Vec<_>=bytes[..336].chunks_exact(16).map(|b|K::from_le_bytes(b).unwrap()).collect();
    let z:[K;10]=f[..10].try_into().unwrap();let k=f[10];let tau=f[11];let alpha=f[12];
    let [sx,sy,zx,zy]:[K;4]=f[13..17].try_into().unwrap();let abc=[sx.mul(zy).sub(sy.mul(zx)),sy.sub(zy),zx.sub(sx)];
    let queries:Vec<_>=bytes[336..].chunks_exact(4).map(|b|u32::from_le_bytes(b.try_into().unwrap())).collect();
    let out=std::path::Path::new(&args[2]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    let start=std::time::Instant::now();let map=basis_transport::transport();
    assert_ne!(K::ONE.add(sx),K::ZERO);assert_ne!(K::ONE.add(zx),K::ZERO);
    let u=sy.mul(K::ONE.add(sx).inv());let v=zy.mul(K::ONE.add(zx).inv());
    let du=K::ONE.add(u.mul(u));let dv=K::ONE.add(v.mul(v));assert_ne!(du,K::ZERO);assert_ne!(dv,K::ZERO);assert_ne!(u,v);
    assert_eq!([K::ONE.sub(u.mul(u)).mul(du.inv()),u.add(u).mul(du.inv())],[sx,sy]);
    assert_eq!([K::ONE.sub(v.mul(v)).mul(dv.inv()),v.add(v).mul(dv.inv())],[zx,zy]);
    let normalized=[K::ONE.add(u.mul(v)),u.mul(v).sub(K::ONE),u.add(v).neg()];
    let scale=v.sub(u).add(v.sub(u)).mul(du.mul(dv).inv());assert_ne!(scale,K::ZERO);
    for i in 0..3{assert_eq!(abc[i],scale.mul(normalized[i]));}
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();
    let roots:Vec<_>=pts.iter().map(|p|p.x.mul(p.x).double().sub(M31::ONE)).collect();
    let mut distinct=roots.clone();distinct.sort_by_key(|x|x.0);distinct.dedup();assert_eq!(distinct.len(),22);
    let raw:Vec<_>=pts.iter().flat_map(|p|[(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)])
        .map(|(x,y)|eval_weights(K::from_cm31(CM31::from_m31(x)),K::from_cm31(CM31::from_m31(y)))).collect();
    let point:Vec<Vec<K>>=corelib::v6_transcript::v6_statement_points(&z).iter().map(|z|{let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,z.to_vec()).unwrap();(0..1024).map(|i|w.weight_at(i)).collect()}).collect();
    let rw=opening_weights::quotient_weights(&z,k,abc,tau,false);let gw=opening_weights::quotient_weights(&z,k,abc,tau,true);
    let l:Vec<_>=(0..C).map(|i|{let mut x=[K::ZERO;C];x[i]=K::ONE;structured_g::mask_eval(&x,&z)}).collect();assert_ne!(l[0],K::ZERO);
    let mut targets=vec![vec![K::ZERO;C+R];T];
    for i in 1..C{targets[i-1][i]=K::ONE;targets[i-1][0]=l[i].neg().mul(l[0].inv());}
    for i in 1..7{targets[270+i-1][C+3+i]=K::ONE;targets[270+i-1][C+3]=alpha.pow(i as u64).neg();}
    let mut factor=vec![K::ONE];for &r in &roots{let mut n=times_x(&factor);for i in 0..factor.len(){n[i]=n[i].sub(factor[i].mul_m31(r));}factor=n;}
    let mut multiples=Vec::new();for d in 22..255{assert_eq!(factor.len(),d+1);assert_ne!(factor[d],K::ZERO);multiples.push(factor.clone());factor=times_x(&factor);}
    let mut matrix=vec![vec![];C+R];let mut qcols=Vec::new();
    eprintln!("R33 phase=source_kernel_and_admissible_chord columns=699");
    for d in 22..255{
        let mut rem=vec![K::ZERO;256];rem[d]=K::ONE;
        for h in(22..=d).rev(){let p=&multiples[h-22];let s=rem[h].mul(p[h].inv());for j in 0..=h{rem[j]=rem[j].sub(s.mul(p[j]));}}
        assert!(rem[22..].iter().all(|&x|x==K::ZERO));let mut v:Vec<_>=rem.iter().map(|x|x.neg()).collect();v[d]=K::ONE;
        for &r in &roots{assert_eq!(corelib::v6_onefold::evaluate_final256_coefficients(&v,r).unwrap(),K::ZERO);}
        for slot in 1..4{
            let q=channel(&v,slot,alpha);let c=chord(&q,abc);let m=map.inverse(&c);let coins=structured_g::mixed_coins(&m);
            let mut unit=vec![K::ZERO;256];unit[d]=K::ONE;let direct=channel(&unit,slot,alpha);
            let normalized_coins=structured_g::mixed_coins(&map.inverse(&chord(&direct,normalized)));
            for i in 0..C{assert_eq!(coins[i],scale.mul(normalized_coins[i]));matrix[i].push(coins[i]);}
            matrix[C].push(structured_g::mask_eval(&coins,&z));for i in 1..3{matrix[C+i].push(dot(&point[i],&m));}
            let pr=polynomial_for_extension(&q,&rw);let pg=polynomial_for_extension(&q,&gw);
            assert_eq!(evaluate(&pr,alpha),K::ZERO);assert_eq!(evaluate(&pg,alpha),K::ZERO);
            assert_eq!(boundary_sum(&pg),k.mul(matrix[C].last().copied().unwrap()).add(k.pow(2).mul(matrix[C+1].last().copied().unwrap())).add(k.pow(3).mul(matrix[C+2].last().copied().unwrap())));
            assert_eq!(dot(&l,&coins),*matrix[C].last().unwrap());
            for i in 0..7{matrix[C+3+i].push(pr[i]);matrix[C+10+i].push(pg[i]);}qcols.push(q);
        }
    }
    let selected:Vec<_>=(0..C).map(|i|{let n=128+3*i;3*(n/4-22)+(if n%4==0{1}else{n%4})-1}).collect();
    let free:Vec<_>=(0..N).filter(|j|!selected.contains(j)).collect();assert_eq!(free.len(),428);
    assert_eq!(&free[..13],&(0..13).collect::<Vec<_>>());
    for j in 0..13{assert!(qcols[j][106..].iter().all(|&x|x==K::ZERO));for i in 0..C{assert_eq!(matrix[i][j],K::ZERO);}}
    let mut core:Vec<Vec<K>>=(0..C).map(|i|{let mut row=matrix[i].clone();row.extend(targets.iter().map(|t|t[i]));row}).collect();
    eprintln!("R33 phase=fixed_minor_elimination core=271 free=428 rhs=276");
    for j in 0..C{
        let col=selected[j];let p=(j..C).find(|&i|core[i][col]!=K::ZERO).expect("R31 fixed minor singular on this actual prefix");core.swap(j,p);
        let inv=core[j][col].inv();for x in &mut core[j]{*x=x.mul(inv);}
        for i in 0..C{if i!=j{let f=core[i][col];if f!=K::ZERO{for h in 0..N+T{core[i][h]=core[i][h].sub(f.mul(core[j][h]));}}}}
    }
    for i in 0..C{for j in 0..C{assert_eq!(core[i][selected[j]],if i==j{K::ONE}else{K::ZERO});}}
    let mut schur=vec![vec![K::ZERO;428+T];R];let mut changed_targets=0;
    for r in 0..R{for c in 0..428+T{
        let col=if c<428{free[c]}else{N+c-428};let mut s=if c<428{matrix[C+r][col]}else{targets[c-428][C+r]};
        for j in 0..C{s=s.sub(matrix[C+r][selected[j]].mul(core[j][col]));}schur[r][c]=s;
        if c>=428&&s!=targets[c-428][C+r]{changed_targets+=1;}
    }}assert!(changed_targets>0,"eliminated core observation must not be discarded");
    assert!(schur[0].iter().all(|&x|x==K::ZERO));
    let original_schur=schur.clone();let mut rows:Vec<Vec<K>>=Vec::new();let mut pivots:Vec<usize>=Vec::new();let mut pivot_rows=Vec::new();
    for(r,mut row)in schur.into_iter().enumerate(){
        for(i,&p)in pivots.iter().enumerate(){let f=row[p];if f!=K::ZERO{for j in 0..428+T{row[j]=row[j].sub(f.mul(rows[i][j]));}}}
        if let Some(p)=(0..428).find(|&j|row[j]!=K::ZERO){let inv=row[p].inv();for x in &mut row{*x=x.mul(inv);}rows.push(row);pivots.push(p);pivot_rows.push(r);}
        else{assert!(row[428..].iter().all(|&x|x==K::ZERO),"residual target compatibility at row {r}");}
    }assert_eq!(pivots.len(),13);
    assert_eq!(pivots,(0..13).collect::<Vec<_>>());
    for r in 0..R{for j in 0..13{assert_eq!(original_schur[r][j],matrix[C+r][j]);}}
    let mut minor_bytes=Vec::new();for &r in &pivot_rows{for &c in &pivots{let mut b=[0;16];original_schur[r][c].write_le_bytes(&mut b);minor_bytes.extend_from_slice(&b);}}
    std::fs::write(out.join("residual-minor.bin"),&minor_bytes).unwrap();
    eprintln!("R33 phase=all_targets_source_reconstruction residual_rank=13");let mut cert=Vec::new();
    for t in 0..T{
        let mut v=vec![K::ZERO;428];for j in(0..13).rev(){v[pivots[j]]=rows[j][428+t].sub(dot(&rows[j][..428],&v));}
        for r in 0..R{assert_eq!(dot(&original_schur[r][..428],&v),original_schur[r][428+t]);}
        let mut x=vec![K::ZERO;N];for i in 0..428{x[free[i]]=v[i];}
        for j in 0..C{x[selected[j]]=core[j][N+t].sub(free.iter().enumerate().fold(K::ZERO,|s,(i,&c)|s.add(core[j][c].mul(v[i]))));}
        for r in 0..C+R{assert_eq!(dot(&matrix[r],&x),targets[t][r],"original observation {r} target {t}");}
        let mut q=vec![K::ZERO;1024];for j in 0..N{if x[j]!=K::ZERO{for r in 0..1024{q[r]=q[r].add(x[j].mul(qcols[j][r]));}}}
        let c=chord(&q,abc);let m=map.inverse(&c);let coins=structured_g::mixed_coins(&m);assert_eq!(coins.as_slice(),&targets[t][..C]);assert_eq!(structured_g::mask_eval(&coins,&z),K::ZERO);
        for i in 1..3{assert_eq!(dot(&point[i],&m),K::ZERO);}for w in &raw{assert_eq!(dot(w,&c),K::ZERO);}
        for(x,y)in[(sx,sy),(zx,zy)]{assert_eq!(dot(&eval_weights(x,y),&c),K::ZERO);}
        assert!(primal(&q,alpha).iter().all(|&x|x==K::ZERO));assert!(q[1021..].iter().all(|&x|x==K::ZERO));
        assert_eq!((0..1024).filter(|&r|map.inactive[r]).fold(K::ZERO,|s,r|s.add(m[r])),K::ZERO);
        assert_eq!(polynomial_for_extension(&q,&rw).as_slice(),&targets[t][C+3..C+10]);assert_eq!(polynomial_for_extension(&q,&gw),[K::ZERO;7]);
        let mut bad=x.clone();bad[selected[0]]=bad[selected[0]].add(K::ONE);assert!(matrix.iter().enumerate().any(|(r,row)|dot(row,&bad)!=targets[t][r]));
        for v in x{let mut b=[0;16];v.write_le_bytes(&mut b);cert.extend_from_slice(&b);}
    }
    std::fs::write(out.join("right-inverse.bin"),&cert).unwrap();let hash:String=Sha256::digest(&cert).iter().map(|b|format!("{b:02x}")).collect();
    std::fs::write(out.join("summary.json"),format!("{{\"core_rank\":271,\"free_columns\":428,\"residual_rows\":17,\"residual_rank\":13,\"selected_columns\":{:?},\"residual_pivot_rows\":{:?},\"residual_pivot_columns\":{:?},\"changed_residual_rhs_entries\":{changed_targets},\"four_source_dependencies_per_column\":true,\"target_basis\":276,\"source_reconstructions\":276,\"original_equations\":{},\"negative_controls\":276,\"right_inverse_bytes\":{},\"right_inverse_sha256\":\"{hash}\",\"actual_ood_parameters_checked\":true,\"universal_residual_coverage\":false,\"full_privacy\":false}}\n",selected,pivot_rows,pivots,(C+R)*T,cert.len())).unwrap();
    println!("R33_G_RESIDUAL core=271 free=428 residual_rank=13 targets=276 original_equations={} source_rechecks=276 negatives=276 changed_rhs={changed_targets} source_prefix_substituted=false full_privacy=false seconds={}",(C+R)*T,start.elapsed().as_secs_f64());
}
