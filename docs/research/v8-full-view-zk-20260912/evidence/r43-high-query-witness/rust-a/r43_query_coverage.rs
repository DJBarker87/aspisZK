//! Targeted scrutiny of query-root symmetries. Not accepted transcript generation.
include!("r37_residual_arithmetic.rs");
fn rank(mut a:Vec<Vec<K>>)->usize {
    let mut r=0;for c in 0..a[0].len(){let Some(p)=(r..a.len()).find(|&i|a[i][c]!=K::ZERO)else{continue};
        a.swap(r,p);let inv=a[r][c].inv();for j in c..a[0].len(){a[r][j]=a[r][j].mul(inv);}
        for i in 0..a.len(){if i==r{continue;}let s=a[i][c];for j in c..a[0].len(){a[i][j]=a[i][j].sub(s.mul(a[r][j]));}}
        r+=1;if r==a.len(){break;}}
    r
}
fn field(seed:u64)->K {let mut x=seed;let mut bytes=[0;16];for i in 0..4{x=x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);bytes[4*i..4*i+4].copy_from_slice(&((x>>32)as u32%2147483647).to_le_bytes());}K::from_le_bytes(&bytes).unwrap()}
fn main(){
    let families:Vec<(&str,Vec<u32>)>=vec![
        ("eleven_opposite_pairs",(0..22).collect()),
        ("twenty_two_unpaired",(0..22).map(|i|2*i).collect()),
        ("spaced_opposite_pairs",(0..11).flat_map(|i|[2*i*997,2*i*997+1]).collect()),
        ("five_quartets_one_pair",(0..20).chain([1000,1001]).collect())];
    let map=basis_transport::transport();let rows=[1,2,3,4,5,6,7,8,10,11,12,13,15];
    let mut total=0;let mut source_columns=0;
    for (name,queries)in families {
        let points=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();
        let roots:Vec<_>=points.iter().map(|pt|pt.x.mul(pt.x).double().sub(M31::ONE)).collect();
        let mut unique:Vec<_>=roots.iter().map(|r|r.0).collect();unique.sort_unstable();unique.dedup();assert_eq!(unique.len(),22);
        if name!="twenty_two_unpaired"{for pair in roots.chunks_exact(2){assert_eq!(pair[0].add(pair[1]),M31::ZERO);}}
        let mut p=vec![K::ONE];for root in roots{let mut next=times_x(&p);for j in 0..p.len(){next[j]=next[j].sub(p[j].mul_m31(root));}p=next;}
        assert_eq!(p.len(),23);let odd_nonzero=p.iter().enumerate().filter(|(i,v)|i%2==1&&**v!=K::ZERO).count();
        if name!="twenty_two_unpaired"{assert_eq!(odd_nonzero,0);}
        for case in 0..8 {
            let z=std::array::from_fn(|i|field(100+case*100+i as u64));let k=field(2001+case);let alpha=field(3001+case);let u=field(4001+case);let v=field(5001+case);
            let abc=[K::ONE.add(u.mul(v)),u.mul(v).sub(K::ONE),u.add(v).neg()];
            let source_points=corelib::v6_transcript::v6_statement_points(&z);
            let weights:Vec<Vec<K>>=source_points.iter().map(|s|{let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,s.to_vec()).unwrap();(0..1024).map(|i|w.weight_at(i)).collect()}).collect();
            let rw=opening_weights::quotient_weights(&z,k,abc,field(6001+case),false);let gw=opening_weights::quotient_weights(&z,k,abc,field(6001+case),true);
            let mut observations=vec![vec![K::ZERO;27];17];let mut shifted=p.clone();
            for col in 0..27 {
                if col>0&&col%3==0{shifted=times_x(&shifted);}
                let slot=col%3+1;let mut q=vec![K::ZERO;1024];for(j,&t)in shifted.iter().enumerate(){q[4*j+slot]=t;q[4*j]=alpha.pow(slot as u64).mul(t).neg();}
                assert!(q[124..].iter().all(|&t|t==K::ZERO));
                let code=chord(&q,abc);assert!(code[128..].iter().all(|&t|t==K::ZERO));let original=map.inverse(&code);
                assert!(structured_g::mixed_coins(&original).iter().all(|&t|t==K::ZERO));
                let mut o=vec![K::ZERO,dot(&original,&weights[1]),dot(&original,&weights[2])];o.extend(polynomial_for_extension(&q,&rw));o.extend(polynomial_for_extension(&q,&gw));
                for r in 0..17{observations[r][col]=o[r];}
                if col<13 {
                    let short=quotient(&p,col,alpha);assert_eq!(&q[..108],&short);
                    let ew:Vec<_>=weights.iter().map(|w|opening_weights::chord_transpose(&map.dual(w),abc)).collect();
                    let wr=std::array::from_fn(|r|k.mul(ew[0][r]).add(k.pow(2).mul(ew[1][r])).add(k.pow(3).mul(ew[2][r])));
                    let wg=std::array::from_fn(|r|k.pow(2).mul(ew[1][r]).add(k.pow(3).mul(ew[2][r])));
                    assert_eq!(&o[3..10],&poly(&short,&wr,true));assert_eq!(&o[10..17],&poly(&short,&wg,true));
                }source_columns+=1;
            }
            let r13=rank(rows.iter().map(|&r|observations[r][..13].to_vec()).collect());
            let r27=rank(rows.iter().map(|&r|observations[r].clone()).collect());let full=rank(observations);
            println!("R43_QUERY_CASE family={name} case={case} odd_coefficients={odd_nonzero} selected13_rank={r13} selected27_rank={r27} full27_rank={full}");total+=1;
        }
    }
    println!("R43_QUERY_COVERAGE cases={total} source_columns={source_columns} accepted_prefix=false universal_rank=false full_privacy=false");
}
