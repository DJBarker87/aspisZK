// Fixed-prefix C1 witness-offset correction, not a complete transcript coupling.
struct R17H1KernelDirection {
    x: Vec<K>,
    q: Vec<K>,
    pad: Vec<K>,
}

struct R17H1AffineSpace {
    h0: Vec<K>,
    h: Vec<K>,
    total: Vec<K>,
    pad: Vec<K>,
    q: Vec<K>,
    rq_base: Vec<K>,
    x: Vec<K>,
    matrix: Vec<Vec<K>>,
    target: Vec<K>,
    rref: Vec<Vec<K>>,
    pivots: Vec<usize>,
    kernel: Vec<R17H1KernelDirection>,
}

struct R17GJointResult {
    g: Vec<K>,
    h1_shift: Vec<K>,
    semantic_delta: [K; 271],
    total: Vec<K>,
}

fn r17_h1_witness_joint_audit(
    h0: &[K], c1: &[Vec<M31>], z: &[K; 10], p: &Prefix,
    kappa: K, alpha: K, queries: &[u32], enc: &CircleEncoder, decoder: &ac::Decoder,
) -> R17H1AffineSpace {
    use r17_coupled_audit::{chord, dot, eval_weights, qvector, reduce};
    let map = crate::r16_basis_transport::transport();
    let scale = p.gamma.pow(26);
    assert_ne!(scale, K::ZERO);
    let mut rest: Vec<_> = h0.iter().map(|&h| h.mul(scale)).collect();
    for c in 0..16 { for r in 0..1024 {
        rest[r] = rest[r].add(p.gamma.pow(c as u64).mul_m31(c1[c][r]));
    }}
    for pt in p.points { assert_eq!(ood(&rest, pt), K::ZERO); }
    let encoded = enc.encode_c2_message(&map.forward(&rest)).unwrap();
    let fibers = corelib::circle_fri::selected_circle_fiber_points_shared(20, &(0..256).collect::<Vec<u32>>()).unwrap();
    let mut values = Vec::new();
    for (i, pt) in fibers.iter().enumerate() {
        for (s, (x,y)) in [(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate() {
            let l = p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y));
            values.push(encoded[4*i+s].mul(l.try_inv().unwrap()));
        }
    }
    let rq_base = decoder.solve_wide(&values);
    assert_eq!(rq_base[1023], K::ZERO);
    assert_eq!(p.abc[1].mul(rq_base[1022]), p.abc[2].mul(rq_base[1021]));
    assert_eq!(chord(&rq_base, p.abc), map.forward(&rest));
    let finals = primal(&rq_base, alpha);
    let rawpoints = corelib::circle_fri::selected_circle_fiber_points_shared(20, queries).unwrap();
    let raw: Vec<_> = rawpoints.iter().flat_map(|pt| [(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)])
        .map(|(x,y)| eval_weights(K::from_cm31(CM31::from_m31(x)), K::from_cm31(CM31::from_m31(y)))).collect();
    let point: Vec<Vec<K>> = corelib::v6_transcript::v6_statement_points(z).iter().map(|z| {
        let mut w = WeightAccumulator::empty(10); w.add_multilinear(K::ONE,z.to_vec()).unwrap();
        (0..1024).map(|i| w.weight_at(i)).collect()
    }).collect();
    let active: Vec<_> = (0..1024).filter(|&r| !map.inactive[r]).collect();
    assert_eq!(active.len(),214);
    let wr=crate::opening_weights::quotient_weights(z,kappa,p.abc,p.tau,false);
    let rq_poly=corelib::sumcheck::polynomial_for_extension(&rq_base,&wr);
    let sent=[0,1,2,3,5,6];
    let mut matrix = vec![vec![K::ZERO;1022];568];
    for j in 0..1022 {
        let mut unit=vec![K::ZERO;1022];unit[j]=K::ONE;
        let q=qvector(&unit,p.abc);let c=chord(&q,p.abc);let m=map.inverse(&c);
        for (i,&r) in active.iter().enumerate(){matrix[i][j]=m[r];}
        matrix[214][j]=(0..1024).filter(|&r|map.inactive[r]).fold(K::ZERO,|s,r|s.add(m[r]));
        for i in 0..88{matrix[215+i][j]=dot(&raw[i],&c);}
        for i in 0..3{matrix[303+i][j]=dot(&point[i],&m);}
        let f=primal(&q,alpha);for i in 0..256{matrix[306+i][j]=f[i];}
        let poly=corelib::sumcheck::polynomial_for_extension(&q,&wr);
        for i in 0..6{matrix[562+i][j]=poly[sent[i]];}
    }
    let hc=map.forward(h0);let mut target=vec![K::ZERO;568];
    for i in 0..6{target[562+i]=rq_poly[sent[i]].mul(scale.inv()).neg();}
    for i in 0..88{target[215+i]=dot(&raw[i],&hc).neg();}
    for i in 0..3{target[303+i]=dot(&point[i],h0).neg();}
    for i in 0..256{target[306+i]=finals[i].mul(scale.inv()).neg();}
    let mut rref=matrix.clone();for i in 0..568{rref[i].push(target[i]);}
    let pivots=reduce(&mut rref,1022);let rank=pivots.len();
    assert!(rref[rank..].iter().all(|r|r[1022]==K::ZERO),"affine H1 joint compatibility rank={rank}");
    let mut x=vec![K::ZERO;1022];for (i,&j) in pivots.iter().enumerate(){x[j]=rref[i][1022];}
    for i in 0..568{assert_eq!(dot(&matrix[i],&x),target[i]);}
    let q=qvector(&x,p.abc);let pad=map.inverse(&chord(&q,p.abc));
    let mut applied=vec![K::ZERO;1024];apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied,&pad).unwrap();assert_eq!(applied,pad);
    let h:Vec<_>=h0.iter().zip(&pad).map(|(&a,&b)|a.add(b)).collect();
    let code=enc.encode_c2_message(&map.forward(&h)).unwrap();
    for &id in queries{for s in 0..4{assert_eq!(code[4*id as usize+s],K::ZERO);}}
    for w in &point{assert_eq!(dot(w,&h),K::ZERO);}
    for pt in corelib::v6_transcript::v6_statement_points(z){assert_eq!(multilinear_evaluate_qm31(&h,&pt).unwrap(),K::ZERO);}
    for pt in p.points{assert_eq!(ood(&h,pt),K::ZERO);}
    let total:Vec<_>=rq_base.iter().zip(&q).map(|(&a,&b)|a.add(scale.mul(b))).collect();
    assert!(primal(&total,alpha).iter().all(|&v|v==K::ZERO));
    assert!(corelib::sumcheck::polynomial_for_extension(&total,&wr).iter().all(|&v|v==K::ZERO),"ordinary first relation zero after actual H1 correction");
    let mut pivoted=vec![false;1022];for &col in &pivots{pivoted[col]=true;}
    let mut kernel=Vec::new();
    for free in 0..1022 {
        if pivoted[free]{continue;}
        let mut direction=vec![K::ZERO;1022];direction[free]=K::ONE;
        for (r,&pivot) in pivots.iter().enumerate(){direction[pivot]=rref[r][free].neg();}
        let qdir=qvector(&direction,p.abc);let pdir=map.inverse(&chord(&qdir,p.abc));
        kernel.push(R17H1KernelDirection{x:direction,q:qdir,pad:pdir});
    }
    println!("R28_H1_WITNESS_JOINT ordinary_first_all7_zero=true rank={rank} equations=568 compatibility_residuals={} raw_zero=88 point_zero=3 ood_zero=2 rest_final_zero=256 gamma26_retained=true fixed_prefix_only=true kernel_directions={}",568-rank,kernel.len());
    R17H1AffineSpace{h0:h0.to_vec(),h,total,pad,q,rq_base,x,matrix,target,rref,pivots,kernel}
}

// Literal old/new terminal enumeration, including nonlinear C1 interactions.
fn r17_witness_semantic_delta(p: &impl PaymentInput, tr: &PoolV1PairLatePublicStatementV1,
    old: &[Vec<K>], new: &[Vec<K>], s: &row::Semantic) -> [K;271] {
    let og=crate::structured_g::mixed_coins(&old[27]);
    let ng=crate::structured_g::mixed_coins(&new[27]);
    let zero=[K::ZERO;271];
    let gd: [K;271]=core::array::from_fn(|i|ng[i].sub(og[i]));
    // Remove G at all three point claims, not just its structured first
    // point. The non-G path now receives no old/new G data at all.
    let mut old_without_g=old.to_vec();old_without_g[27].fill(K::ZERO);
    let mut new_without_g=new.to_vec();new_without_g[27].fill(K::ZERO);
    let mut coords=[K::ZERO;271];let mut carry=K::ZERO;
    for r in 0..10 {
        let left=9-r;let mut samples=[K::ZERO;28];
        for x in 0..28 {let mut z=s.z;z[r]=sc(x as u32);
            for assignment in 0..1usize<<left {
                for j in 0..left {z[r+1+j]=sc(((assignment>>(left-1-j))&1)as u32);}
                let literal=terminal_with_g(p,tr,new,&z,s,&ng).sub(terminal_with_g(p,tr,old,&z,s,&og));
                let without_g=terminal_with_g(p,tr,&new_without_g,&z,s,&zero).sub(terminal_with_g(p,tr,&old_without_g,&z,s,&zero));
                let split=without_g.add(crate::structured_g::mask_eval(&gd,&z));
                assert_eq!(literal,split,"source G independence r={r} x={x}");
                samples[x]=samples[x].add(split);
            }
        }
        let poly=interpolate_degree27(&samples);
        if r==0 {carry=state_only_boundary_sum(&poly);coords[0]=carry;}
        assert_eq!(state_only_boundary_sum(&poly),carry,"witness semantic boundary {r}");
        coords[1+27*r]=poly[0].sub(carry.half());
        for k in 2..28 {coords[1+27*r+k-1]=poly[k];}
        carry=evaluate_state_only_polynomial(&poly,s.z[r]);
    }
    assert_eq!(carry,terminal_with_g(p,tr,new,&s.z,s,&ng).sub(terminal_with_g(p,tr,old,&s.z,s,&og)));
    assert_eq!(crate::structured_g::mask_eval(&coords,&s.z),carry);
    coords
}

fn r17_g_witness_audit(delta: &[K;271], rq: &[K], z: &[K;10], p: &Prefix,
    kappa: K, alpha: K, beta: K, queries: &[u32], enc: &CircleEncoder,
    h1_domain: Option<(&R17H1AffineSpace, &[Vec<K>])>) -> R17GJointResult {
    use r17_coupled_audit::{chord,dot,eval_weights,qvector,reduce};
    let map=crate::r16_basis_transport::transport();
    let gw=crate::opening_weights::quotient_weights(z,kappa,p.abc,p.tau,true);
    let rw=crate::opening_weights::quotient_weights(z,kappa,p.abc,p.tau,false);
    let wr:Vec<_>=(0..1024).map(|i|rw.weight_at(i)).collect();
    let wg:Vec<_>=(0..1024).map(|i|gw.weight_at(i)).collect();
    let dw:Vec<_>=wg.iter().zip(&wr).map(|(&g,&r)|g.sub(r)).collect();
    assert_eq!(dot(rq,&wr),K::ZERO,"new p0 affine target after C1/H1");
    let mut wb=WeightAccumulator::empty(10);
    wb.add_dense(wr.iter().zip(&wg).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect()).unwrap();
    let rp=corelib::sumcheck::polynomial_for_extension(rq,&wb).map(|x|K::ONE.sub(beta).mul(x));
    assert_eq!(corelib::sumcheck::evaluate(&rp,alpha),K::ZERO);
    assert_eq!(crate::structured_g::mask_eval(delta,z),K::ZERO,"retained terminal");
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,queries).unwrap();
    let raw:Vec<_>=pts.iter().flat_map(|p|[(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)])
        .map(|(x,y)|eval_weights(K::from_cm31(CM31::from_m31(x)),K::from_cm31(CM31::from_m31(y)))).collect();
    let mut point:Vec<Vec<K>>=corelib::v6_transcript::v6_statement_points(z).iter().map(|z|{
        let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,z.to_vec()).unwrap();
        (0..1024).map(|i|w.weight_at(i)).collect()
    }).collect();point[0]=crate::structured_g::mask_weights(z);
    let mixing:Vec<_>=(0..271).map(crate::structured_g::mixing_row).collect();
    let mut matrix=vec![vec![K::ZERO;1022];626];
    for j in 0..1022 {
        let mut unit=vec![K::ZERO;1022];unit[j]=K::ONE;
        let q=qvector(&unit,p.abc);let c=chord(&q,p.abc);let m=map.inverse(&c);
        for i in 0..271{matrix[i][j]=dot(&mixing[i],&m);}
        for i in 0..88{matrix[271+i][j]=dot(&raw[i],&c);}
        for i in 0..3{matrix[359+i][j]=dot(&point[i],&m);}
        let f=primal(&q,alpha);for i in 0..256{matrix[362+i][j]=f[i];}
        matrix[618][j]=(0..1024).filter(|&r|map.inactive[r]).fold(K::ZERO,|s,r|s.add(m[r]));
        matrix[625][j]=dot(&dw,&q);
        let poly=corelib::sumcheck::polynomial_for_extension(&q,&wb).map(|x|beta.mul(x));
        for (i,k) in [0,1,2,3,5,6].into_iter().enumerate(){matrix[619+i][j]=poly[k];}
    }
    let build_target=|semantic:&[K;271],total:&[K]|{
        let mut out=vec![K::ZERO;626];
        for i in 0..271{out[i]=semantic[i].neg();}
        let scale=p.gamma.pow(27);assert_ne!(scale,K::ZERO);
        let poly=corelib::sumcheck::polynomial_for_extension(total,&wb).map(|x|K::ONE.sub(beta).mul(x));
        for (i,k) in [0,1,2,3,5,6].into_iter().enumerate(){out[619+i]=poly[k].mul(scale.inv()).neg();}
        out[625]=dot(&dw,total).mul(scale.inv());
        out
    };
    let mut target=build_target(delta,rq);
    let baseline_target=target.clone();
    let mut reduced=matrix.clone();for i in 0..626{reduced[i].push(target[i]);}
    let mut ledger=vec![vec![K::ZERO;626];626];
    for i in 0..626{ledger[i][i]=K::ONE;}
    let mut pivots=vec![];
    for col in 0..1022 {
        let r=pivots.len();
        let Some(pivot_row)=(r..626).find(|&i|reduced[i][col]!=K::ZERO) else {continue;};
        reduced.swap(r,pivot_row);ledger.swap(r,pivot_row);
        let inv=reduced[r][col].inv();
        for v in &mut reduced[r][col..]{*v=v.mul(inv);}
        for v in &mut ledger[r]{*v=v.mul(inv);}
        let row=reduced[r].clone();let rowop=ledger[r].clone();
        for i in 0..626 {
            if i==r{continue;}
            let factor=reduced[i][col];if factor==K::ZERO{continue;}
            for j in col..row.len(){reduced[i][j]=reduced[i][j].sub(factor.mul(row[j]));}
            for j in 0..626{ledger[i][j]=ledger[i][j].sub(factor.mul(rowop[j]));}
        }
        pivots.push(col);
        if pivots.len()==626{break;}
    }
    let rank=pivots.len();
    let incompatible:Vec<usize>=(rank..626).filter(|&r|reduced[r][1022]!=K::ZERO).collect();
    println!("R117_G_BASELINE rows=626 columns=1022 rank={rank} residual_rows={} incompatible_rhs={}",626-rank,incompatible.len());
    let mut h1_shift=vec![K::ZERO;1024];
    let mut final_delta=core::array::from_fn(|i|delta[i]);
    let mut final_total=rq.to_vec();
    if let Some((h1,semantic_map))=h1_domain {
        assert_eq!(semantic_map.len(),271);
        assert!(semantic_map.iter().all(|row|row.len()==1024));
        let variables=h1.kernel.len();
        let residual_count=626-rank;
        let scale26=p.gamma.pow(26);let scale27=p.gamma.pow(27);
        assert_ne!(scale26,K::ZERO);assert_ne!(p.gamma,K::ZERO);
        let relation_factor=K::ONE.sub(beta).mul(p.gamma.inv());
        let mut b_columns=vec![vec![K::ZERO;626];variables];
        for (j,dir) in h1.kernel.iter().enumerate() {
            for i in 0..271{b_columns[j][i]=dot(&semantic_map[i],&dir.pad).neg();}
            let poly=corelib::sumcheck::polynomial_for_extension(&dir.q,&wb);
            for (i,k) in [0,1,2,3,5,6].into_iter().enumerate(){b_columns[j][619+i]=relation_factor.mul(poly[k]).neg();}
            b_columns[j][625]=dot(&dw,&dir.q).mul(p.gamma.inv());
        }
        let mut schur=vec![vec![K::ZERO;variables+1];residual_count];
        for rr in 0..residual_count {
            let gr=rank+rr;
            for j in 0..variables{schur[rr][j]=dot(&ledger[gr],&b_columns[j]);}
            schur[rr][variables]=reduced[gr][1022].neg();
        }
        let schur_original=schur.clone();
        let mut schur_ledger=vec![vec![K::ZERO;residual_count];residual_count];
        for i in 0..residual_count{schur_ledger[i][i]=K::ONE;}
        let mut schur_pivots=Vec::new();
        for col in 0..variables {
            let rr=schur_pivots.len();
            let Some(pr)=(rr..residual_count).find(|&r|schur[r][col]!=K::ZERO) else {continue;};
            schur.swap(rr,pr);schur_ledger.swap(rr,pr);
            let inv=schur[rr][col].inv();
            for v in &mut schur[rr][col..=variables]{*v=v.mul(inv);}
            for v in &mut schur_ledger[rr]{*v=v.mul(inv);}
            let row=schur[rr].clone();let rowop=schur_ledger[rr].clone();
            for r in 0..residual_count {
                if r==rr{continue;}
                let factor=schur[r][col];if factor==K::ZERO{continue;}
                for j in col..=variables{schur[r][j]=schur[r][j].sub(factor.mul(row[j]));}
                for j in 0..residual_count{schur_ledger[r][j]=schur_ledger[r][j].sub(factor.mul(rowop[j]));}
            }
            schur_pivots.push(col);
            if schur_pivots.len()==residual_count{break;}
        }
        let schur_rank=schur_pivots.len();
        let schur_incompatible:Vec<usize>=(schur_rank..residual_count).filter(|&r|schur[r][variables]!=K::ZERO).collect();
        println!("R117_H1_G_SCHUR residual_rows={residual_count} h1_kernel_variables={variables} rank={schur_rank} incompatible_rows={}",schur_incompatible.len());
        if let Some(&bad)=schur_incompatible.first() {
            let obstruction=&schur_ledger[bad];
            for j in 0..variables{assert_eq!((0..residual_count).fold(K::ZERO,|a,r|a.add(obstruction[r].mul(dot(&ledger[rank+r],&b_columns[j])))),K::ZERO,"full G Schur obstruction column {j}");}
            let rhs=(0..residual_count).fold(K::ZERO,|a,r|a.add(obstruction[r].mul(schur_original[r][variables])));
            assert_eq!(rhs,schur[bad][variables],"Schur obstruction reproduces reduced RHS from original system");
            assert_ne!(rhs,K::ZERO,"full G Schur obstruction RHS");
            let push_k=|bytes:&mut Vec<u8>,x:K|{for w in [x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]{bytes.extend_from_slice(&w.to_le_bytes());}};
            let gpath=std::env::var_os("ASPIS_R117_G_CERT_PATH").expect("explicit G baseline certificate path for Schur failure");
            let mut gb=Vec::with_capacity(64+626*1022*16+626*16+626*626*16);
            gb.extend_from_slice(b"R117GBASESCHUR1\0");gb.extend_from_slice(&(626u32).to_le_bytes());gb.extend_from_slice(&(1022u32).to_le_bytes());gb.extend_from_slice(&(rank as u32).to_le_bytes());gb.extend_from_slice(&(residual_count as u32).to_le_bytes());
            for &c in &pivots{gb.extend_from_slice(&(c as u32).to_le_bytes());}
            for row in &matrix{for &x in row{push_k(&mut gb,x);}}
            for &x in &baseline_target{push_k(&mut gb,x);}
            for row in &ledger{for &x in row{push_k(&mut gb,x);}}
            for r in rank..626{push_k(&mut gb,reduced[r][1022]);}
            std::fs::write(gpath,&gb).expect("write full baseline G matrix and row ledger");
            let spath=std::env::var_os("ASPIS_R117_SCHUR_CERT_PATH").expect("explicit full Schur certificate path");
            let mut sb=Vec::new();sb.extend_from_slice(b"R117H1GALLSCHUR1\0");
            for n in [residual_count,variables,schur_rank,h1.pivots.len(),h1.kernel.len()]{sb.extend_from_slice(&(n as u32).to_le_bytes());}
            push_k(&mut sb,beta);
            for row in &h1.matrix{for &x in row{push_k(&mut sb,x);}}
            for &x in &h1.target{push_k(&mut sb,x);}
            for row in &h1.rref{for &x in row{push_k(&mut sb,x);}}
            for &x in &h1.pivots{sb.extend_from_slice(&(x as u32).to_le_bytes());}
            for &x in &h1.x{push_k(&mut sb,x);}
            for row in semantic_map{for &x in row{push_k(&mut sb,x);}}
            for dir in &h1.kernel{for &x in &dir.x{push_k(&mut sb,x);}for &x in &dir.q{push_k(&mut sb,x);}for &x in &dir.pad{push_k(&mut sb,x);}}
            for col in &b_columns{for &x in col{push_k(&mut sb,x);}}
            for row in &schur_original{for &x in row{push_k(&mut sb,x);}}
            for row in &schur{for &x in row{push_k(&mut sb,x);}}
            for row in &schur_ledger{for &x in row{push_k(&mut sb,x);}}
            for &x in obstruction{push_k(&mut sb,x);}
            for &x in &schur_pivots{sb.extend_from_slice(&(x as u32).to_le_bytes());}
            std::fs::write(spath,&sb).expect("write full H1/G Schur obstruction and basis data");
            assert!(false,"all G residual rows incompatible with H1 kernel; Schur rank={schur_rank}/{residual_count} variables={variables} obstruction_rhs={rhs:?}");
        }
        let mut coeff=vec![K::ZERO;variables];
        for (r,&col) in schur_pivots.iter().enumerate(){coeff[col]=schur[r][variables];}
        let mut x_h1=h1.x.clone();
        for (j,dir) in h1.kernel.iter().enumerate(){for k in 0..1022{x_h1[k]=x_h1[k].add(coeff[j].mul(dir.x[k]));}}
        for i in 0..568{assert_eq!(dot(&h1.matrix[i],&x_h1),h1.target[i],"retained original H1 row {i}");}
        let q_h1=qvector(&x_h1,p.abc);let pad_h1=map.inverse(&chord(&q_h1,p.abc));
        let mut applied=vec![K::ZERO;1024];apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied,&pad_h1).unwrap();assert_eq!(applied,pad_h1);
        let h_final:Vec<_>=h1.h0.iter().zip(&pad_h1).map(|(&a,&b)|a.add(b)).collect();
        let code=enc.encode_c2_message(&map.forward(&h_final)).unwrap();
        for &id in queries{for slot in 0..4{assert_eq!(code[4*id as usize+slot],K::ZERO);}}
        let point_rows:Vec<Vec<K>>=corelib::v6_transcript::v6_statement_points(z).iter().map(|pt|{
            let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,pt.to_vec()).unwrap();
            (0..1024).map(|i|w.weight_at(i)).collect()
        }).collect();
        for w in &point_rows{assert_eq!(dot(w,&h_final),K::ZERO);}
        for pt in corelib::v6_transcript::v6_statement_points(z){assert_eq!(multilinear_evaluate_qm31(&h_final,&pt).unwrap(),K::ZERO);}
        for pt in p.points{assert_eq!(ood(&h_final,pt),K::ZERO);}
        final_total=h1.rq_base.iter().zip(&q_h1).map(|(&a,&b)|a.add(scale26.mul(b))).collect();
        assert_eq!(dot(&final_total,&wr),K::ZERO,"p0 preserved by all H1 kernel directions");
        assert!(primal(&final_total,alpha).iter().all(|&v|v==K::ZERO));
        assert!(corelib::sumcheck::polynomial_for_extension(&final_total,&rw).iter().all(|&v|v==K::ZERO));
        for i in 0..1024{h1_shift[i]=pad_h1[i].sub(h1.pad[i]);}
        final_delta=core::array::from_fn(|i|delta[i].add(dot(&semantic_map[i],&h1_shift)));
        target=build_target(&final_delta,&final_total);
        for i in 0..626 {
            let predicted=(0..variables).fold(baseline_target[i],|a,j|a.add(coeff[j].mul(b_columns[j][i])));
            assert_eq!(target[i],predicted,"all G target changes represented by H1 kernel B row {i}");
        }
        for i in 271..619{assert_eq!(target[i],baseline_target[i],"G raw/point/final/balance rows unchanged {i}");}
        let transformed:Vec<_>=(0..626).map(|r|dot(&ledger[r],&target)).collect();
        let final_incompatible:Vec<_>=(rank..626).filter(|&r|transformed[r]!=K::ZERO).collect();
        println!("R117_G_COUPLED_TARGET residual_rows={residual_count} corrected_incompatible_rows={} h1_kernel_variables={variables}",final_incompatible.len());
        assert!(final_incompatible.is_empty(),"G target compatibility after all-row H1 Schur");
        let mut recomputed=vec![K::ZERO;626];
        for i in 0..271{recomputed[i]=final_delta[i].neg();}
        let relation_poly=corelib::sumcheck::polynomial_for_extension(&final_total,&wb).map(|v|K::ONE.sub(beta).mul(v));
        for (i,k) in [0,1,2,3,5,6].into_iter().enumerate(){recomputed[619+i]=relation_poly[k].mul(scale27.inv()).neg();}
        recomputed[625]=dot(&dw,&final_total).mul(scale27.inv());
        assert_eq!(recomputed,target,"recomputed complete G source target");
        // Reuse the one G matrix/ledger: transform only the corrected RHS.
    } else {
        if let Some(&bad)=incompatible.first(){
            let coeff=&ledger[bad];
            let mut support_groups=[0usize;7];
            for (i,&x) in coeff.iter().enumerate(){if x!=K::ZERO{let g=match i{0..=270=>0,271..=358=>1,359..=361=>2,362..=617=>3,618=>4,619..=624=>5,_=>6};support_groups[g]+=1;}}
            for j in 0..1022{let sum=(0..626).fold(K::ZERO,|a,i|a.add(coeff[i].mul(matrix[i][j])));assert_eq!(sum,K::ZERO,"left-kernel certificate original column {j}");}
            let rhs=(0..626).fold(K::ZERO,|a,i|a.add(coeff[i].mul(target[i])));
            assert_eq!(rhs,reduced[bad][1022]);assert_ne!(rhs,K::ZERO);
            println!("R117_G_LEFT_KERNEL checked_original_columns=1022 rhs_nonzero=true support_semantic_raw_point_final_balance_relation_p2={support_groups:?}");
            if let Some(path)=std::env::var_os("ASPIS_R117_G_CERT_PATH"){
                let mut bytes=Vec::with_capacity(32+626*1022*16+626*32);
                bytes.extend_from_slice(b"R117GLEFTKERNEL1\0");bytes.extend_from_slice(&(626u32).to_le_bytes());bytes.extend_from_slice(&(1022u32).to_le_bytes());
                let push_k=|bytes:&mut Vec<u8>,x:K|{for w in [x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]{bytes.extend_from_slice(&w.to_le_bytes());}};
                for row in &matrix{for &x in row{push_k(&mut bytes,x);}}
                for &x in &target{push_k(&mut bytes,x);}
                for &x in coeff{push_k(&mut bytes,x);}
                std::fs::write(path,&bytes).expect("write G left-kernel evidence");
            }
        }
        assert!(incompatible.is_empty(),"affine G witness compatibility");
    }
    // For either route, derive the solution from the already retained G row ledger.
    let transformed:Vec<_>=(0..626).map(|r|dot(&ledger[r],&target)).collect();
    let final_incompatible:Vec<usize>=(rank..626).filter(|&r|transformed[r]!=K::ZERO).collect();
    assert!(final_incompatible.is_empty(),"final G target must satisfy every left-kernel row");
    let mut x=vec![K::ZERO;1022];for (r,&col) in pivots.iter().enumerate(){x[col]=transformed[r];}
    for i in 0..626{assert_eq!(dot(&matrix[i],&x),target[i],"original G row {i}");}
    let q=qvector(&x,p.abc);let g=map.inverse(&chord(&q,p.abc));
    let gc=crate::structured_g::mixed_coins(&g);
    for i in 0..271{assert_eq!(gc[i].add(final_delta[i]),K::ZERO);}
    let scale=p.gamma.pow(27);
    assert_eq!(scale.mul(dot(&dw,&q)),dot(&dw,&final_total),"new p2 source equation");
    let final_rp=corelib::sumcheck::polynomial_for_extension(&final_total,&wb).map(|x|K::ONE.sub(beta).mul(x));
    let gp=corelib::sumcheck::polynomial_for_extension(&q,&wb).map(|x|beta.mul(x));
    for i in 0..7{assert_eq!(final_rp[i].add(scale.mul(gp[i])),K::ZERO);}
    let code=enc.encode_c2_message(&map.forward(&g)).unwrap();
    for &id in queries{for s in 0..4{assert_eq!(code[4*id as usize+s],K::ZERO);}}
    for pt in p.points{assert_eq!(ood(&g,pt),K::ZERO);}
    for pt in corelib::v6_transcript::v6_statement_points(z).iter().skip(1){assert_eq!(multilinear_evaluate_qm31(&g,pt).unwrap(),K::ZERO);}
    assert_eq!(crate::structured_g::mask_eval(&gc,z),K::ZERO);
    assert!(primal(&q,alpha).iter().all(|&v|v==K::ZERO));
    println!("R19_G_WITNESS_JOINT equations=626 rank={rank} corrected_incompatible_rows=0 new_p0_checked=true new_p2_checked=true semantic_cancel=271 relation_cancel=7 raw_zero=88 point_zero=3 ood_zero=2 final_zero=256 fixed_prefix_only=true");
    R17GJointResult{g,h1_shift,semantic_delta:final_delta,total:final_total}
}

// First affine helper step only: retain both OOD values with a legal pad.
// Raw, point, final and semantic observations still require joint correction.
fn r17_h1_two_point_pad(target: [K;2], points: [Point;2]) -> Option<Vec<K>> {
    let map=crate::r16_basis_transport::transport();
    let (j,t0,t1)=if points[1].y!=points[0].y {
        (1,points[0].y,points[1].y)
    } else if points[1].x!=points[0].x {
        (2,points[0].x,points[1].x)
    } else {return None;};
    let b=target[1].sub(target[0]).mul(t1.sub(t0).try_inv().unwrap());
    let a=target[0].sub(b.mul(t0));
    let mut pad=vec![K::ZERO;1024];
    for (k,v) in [(0,a),(j,b)] {
        let r=map.order[k];assert!(map.inactive[r] && r!=1023);
        pad[r]=pad[r].add(v);pad[1023]=pad[1023].sub(v);
    }
    let mut expected=vec![K::ZERO;1024];expected[0]=a;expected[j]=b;
    assert_eq!(map.forward(&pad),expected,"legal H1 1/x/y basis transport");
    let mut applied=vec![K::ZERO;1024];
    apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied,&pad).unwrap();
    assert_eq!(applied,pad);
    for i in 0..2{assert_eq!(ood(&pad,points[i]),target[i]);}
    Some(pad)
}

fn r17_h1_witness_ood_audit(before: &[K], after: &[K], points: [Point; 2]) -> Vec<K> {
    assert_eq!(before.len(), 1024);
    assert_eq!(after.len(), 1024);
    let map = crate::r16_basis_transport::transport();
    let base: Vec<_> = after.iter().zip(before).map(|(&a, &b)| a.sub(b)).collect();
    let target = [ood(&base, points[0]).neg(), ood(&base, points[1]).neg()];
    // Exercise both coordinate branches on distinct circle points, and
    // retain a coincident-point rejection control. Not a schedule search.
    let yp=[Point{x:K::ZERO,y:K::ONE},Point{x:K::ZERO,y:K::ONE.neg()}];
    let xp=[Point{x:K::ONE,y:K::ZERO},Point{x:K::ONE.neg(),y:K::ZERO}];
    assert!(r17_h1_two_point_pad([sc(7),sc(11)],yp).is_some());
    assert!(r17_h1_two_point_pad([sc(7),sc(11)],xp).is_some());
    assert!(r17_h1_two_point_pad([K::ZERO,K::ONE],[xp[0],xp[0]]).is_none());
    let pad=r17_h1_two_point_pad(target,points).expect("source OOD points must differ");
    let mut applied = vec![K::ZERO; 1024];
    apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied, &pad).unwrap();
    assert_eq!(applied, pad);
    let result: Vec<_> = base.iter().zip(&pad).map(|(&a, &b)| a.add(b)).collect();
    for i in 0..2 { assert_eq!(ood(&result, points[i]), K::ZERO); }
    for r in 0..1024 { if !map.inactive[r] { assert_eq!(result[r], base[r]); } }
    println!("R17_H1_WITNESS_OOD coverage=explicit_distinct_point_interpolation directions_used=2 coordinate_branches_checked=2 coincident_rejected=true source_pad_checked=true retained_ood=2 active_helper_offset_retained=true fixed_prefix_only=true");
    result
}

fn r17_c1_witness_audit(
    base: &[Vec<M31>],
    z: &[K; 10],
    points: [Point; 2],
    queries: &[u32],
    enc: &CircleEncoder,
) -> Vec<Vec<M31>> {
    use r17_coupled_audit::{dot,qvector};
    let map = crate::r16_basis_transport::transport();
    let mut index = vec![0; 1024];
    for (j, &r) in map.order.iter().enumerate() { index[r] = j; }
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let mut balanced = base.to_vec();
    for col in 0..16 {
        let dependent = cells.iter().filter(|c| c.column as usize == col && map.inactive[c.row as usize]).last().unwrap().row as usize;
        assert_eq!(dependent, 1023);
        balanced[col][dependent] = (0..1024).filter(|&r| map.inactive[r] && r != dependent)
            .fold(M31::ZERO, |a, r| a.add(base[col][r])).neg();
    }
    let base = balanced.as_slice();
    let point_weights: Vec<Vec<K>> = corelib::v6_transcript::v6_statement_points(z).iter().map(|p| {
        let mut w = WeightAccumulator::empty(10); w.add_multilinear(K::ONE, p.to_vec()).unwrap();
        (0..1024).map(|i| w.weight_at(i)).collect()
    }).collect();
    let ood_weights: Vec<Vec<K>> = points.iter().map(|p| {
        let mut f = [K::ZERO; 10]; f[0] = p.y; f[1] = p.x;
        for i in 2..10 { f[i] = f[i - 1].square().mul_m31(M31(2)).sub(K::ONE); }
        (0..1024).map(|j| (0..10).filter(|&i| j & (1 << i) != 0).fold(K::ONE, |a, i| a.mul(f[i]))).collect()
    }).collect();
    let raw: Vec<Vec<M31>> = queries.iter().flat_map(|&q| (0..4).map(move |s| 4 * q as usize + s))
        .map(|pos| (0..1024).map(|j| enc.encode_c1_basis_value(j, pos).unwrap()).collect()).collect();
    let limbs = |v: K| [v.c0.a, v.c0.b, v.c1.a, v.c1.b];
    let dot_m31 = |a: &[M31], b: &[M31]| a.iter().zip(b).fold(M31::ZERO, |sum, (&x, &y)| sum.add(x.mul(y)));
    let qdot = |a: &[K], b: &[M31]| a.iter().zip(b).fold(K::ZERO, |s, (&a, &b)| s.add(a.mul_m31(b)));
    let boolean_point = |row: usize| -> [K; 10] {
        core::array::from_fn(|coordinate| if (row >> (9 - coordinate)) & 1 == 0 { K::ZERO } else { K::ONE })
    };
    let zero_mask_only = [K::ZERO; 10];
    let mut result = base.to_vec();
    let mut changed = 0;
    let mut rows_by_col: Vec<Vec<usize>> = Vec::with_capacity(16);
    let mut matrices: Vec<Vec<Vec<M31>>> = Vec::with_capacity(16);
    let mut targets: Vec<Vec<M31>> = Vec::with_capacity(16);
    let mut solutions: Vec<Vec<M31>> = Vec::with_capacity(16);
    let mut initial_covectors_by_col: Vec<Vec<K>> = Vec::with_capacity(16);
    let mut pivots_by_col: Vec<Vec<usize>> = Vec::with_capacity(16);
    let mut free_by_col: Vec<Vec<usize>> = Vec::with_capacity(16);
    let mut kernel_directions: Vec<(usize, usize, Vec<M31>)> = Vec::new();
    let mut schur_columns: Vec<[M31; 4]> = Vec::new();
    let mut total_initial_delta = K::ZERO;

    // First solve the original 108 C1 observation equations independently.
    // Retain every free-variable kernel direction for the aggregate claim solve.
    for col in 0..16 {
        changed += base[col].iter().filter(|&&v| v != M31::ZERO).count();
        let rows: Vec<_> = cells.iter().filter(|c| c.column as usize == col && c.row != 1023 && !(col == 3 && c.row == 1014)).map(|c| c.row as usize).collect();
        let width = rows.len();
        let unit_c1: [K; 16] = core::array::from_fn(|j| if j == col { K::ONE } else { K::ZERO });
        let initial_covectors: Vec<K> = (0..1024).map(|row| corelib::state_only_hiding::state_only_selected_mask_value(
            &unit_c1, &zero_mask_only, K::ZERO, &boolean_point(row),
        )).collect();
        let mut matrix = vec![vec![M31::ZERO; width]; 108];
        for (k, &r) in rows.iter().enumerate() {
            let j = index[r];
            for i in 0..88 { matrix[i][k] = raw[i][j]; }
            for (i, w) in point_weights.iter().enumerate() {
                let v = if map.inactive[r] { w[r].sub(w[1023]) } else { w[r] };
                for (b, v) in limbs(v).into_iter().enumerate() { matrix[88 + 4 * i + b][k] = v; }
            }
            for (i, w) in ood_weights.iter().enumerate() {
                for (b, v) in limbs(w[j]).into_iter().enumerate() { matrix[100 + 4 * i + b][k] = v; }
            }
            let mut unit = vec![M31::ZERO; 1024]; unit[r] = M31::ONE;
            if map.inactive[r] { unit[1023] = M31::ONE.neg(); }
            let transformed = map.forward(&unit);
            assert_eq!(transformed[j], M31::ONE);
            assert_eq!(transformed.iter().filter(|&&v| v != M31::ZERO).count(), 1);
        }
        let encoded = map.forward(&base[col]);
        let mut target = vec![M31::ZERO; 108];
        for i in 0..88 { target[i] = dot_m31(&raw[i], &encoded).neg(); }
        for (i, w) in point_weights.iter().enumerate() {
            for (b, v) in limbs(qdot(w, &base[col])).into_iter().enumerate() { target[88 + 4 * i + b] = v.neg(); }
        }
        for (i, w) in ood_weights.iter().enumerate() {
            for (b, v) in limbs(qdot(w, &encoded)).into_iter().enumerate() { target[100 + 4 * i + b] = v.neg(); }
        }
        let mut reduced = matrix.clone();
        for (i, row) in reduced.iter_mut().enumerate() { row.push(target[i]); }
        let mut pivots = vec![];
        for k in 0..width {
            let rank = pivots.len();
            let Some(p) = (rank..108).find(|&r| reduced[r][k] != M31::ZERO) else { continue; };
            reduced.swap(rank, p);
            let inv = reduced[rank][k].inv();
            for v in &mut reduced[rank][k..] { *v = v.mul(inv); }
            let pivot = reduced[rank].clone();
            for r in 0..108 {
                if r == rank { continue; }
                let f = reduced[r][k]; if f == M31::ZERO { continue; }
                for j in k..=width { reduced[r][j] = reduced[r][j].sub(f.mul(pivot[j])); }
            }
            pivots.push(k);
            if pivots.len() == 108 { break; }
        }
        let rank = pivots.len();
        assert!(reduced[rank..108].iter().all(|row| row[width] == M31::ZERO), "original C1 target incompatible col={col} rank={rank}");
        let mut solution = vec![M31::ZERO; width];
        for (r, &k) in pivots.iter().enumerate() { solution[k] = reduced[r][width]; }
        for i in 0..108 { assert_eq!(dot_m31(&matrix[i], &solution), target[i]); }
        for (k, &r) in rows.iter().enumerate() {
            result[col][r] = result[col][r].add(solution[k]);
            if map.inactive[r] { result[col][1023] = result[col][1023].sub(solution[k]); }
        }
        let particular_initial = initial_covectors.iter().zip(&result[col]).fold(K::ZERO, |sum, (&w, &v)| sum.add(w.mul_m31(v)));
        total_initial_delta = total_initial_delta.add(particular_initial);
        for free in 0..width {
            if pivots.contains(&free) { continue; }
            let mut direction = vec![M31::ZERO; width]; direction[free] = M31::ONE;
            for (r, &pivot_col) in pivots.iter().enumerate() { direction[pivot_col] = reduced[r][free].neg(); }
            let mut effect = K::ZERO;
            for (k, &row) in rows.iter().enumerate() {
                let covector = if map.inactive[row] { initial_covectors[row].sub(initial_covectors[1023]) } else { initial_covectors[row] };
                effect = effect.add(covector.mul_m31(direction[k]));
            }
            for i in 0..108 { assert_eq!(dot_m31(&matrix[i], &direction), M31::ZERO, "C1 kernel direction original row {i}"); }
            schur_columns.push(limbs(effect));
            kernel_directions.push((col, free, direction));
        }
        let free_cols: Vec<usize> = (0..width).filter(|k| !pivots.contains(k)).collect();
        assert_eq!(free_cols.len(), width - rank);
        rows_by_col.push(rows);
        matrices.push(matrix);
        targets.push(target);
        solutions.push(solution);
        initial_covectors_by_col.push(initial_covectors);
        pivots_by_col.push(pivots);
        free_by_col.push(free_cols);
    }

    // Choose among the original C1 solution cosets to preserve the one actual
    // aggregate initial claim, without forcing each column contribution to zero.
    let variables = schur_columns.len();
    let mut schur = vec![vec![M31::ZERO; variables + 1]; 4];
    for (j, column) in schur_columns.iter().enumerate() { for limb in 0..4 { schur[limb][j] = column[limb]; } }
    let wanted = limbs(total_initial_delta.neg());
    for limb in 0..4 { schur[limb][variables] = wanted[limb]; }
    let mut ledger = vec![vec![M31::ZERO; 4]; 4];
    for i in 0..4 { ledger[i][i] = M31::ONE; }
    let mut pivots = vec![];
    for col in 0..variables {
        let rank = pivots.len();
        let Some(p) = (rank..4).find(|&r| schur[r][col] != M31::ZERO) else { continue; };
        schur.swap(rank, p); ledger.swap(rank, p);
        let inv = schur[rank][col].inv();
        for v in &mut schur[rank][col..] { *v = v.mul(inv); }
        for v in &mut ledger[rank] { *v = v.mul(inv); }
        let pivot = schur[rank].clone(); let rowop = ledger[rank].clone();
        for r in 0..4 {
            if r == rank { continue; }
            let f = schur[r][col]; if f == M31::ZERO { continue; }
            for j in col..=variables { schur[r][j] = schur[r][j].sub(f.mul(pivot[j])); }
            for j in 0..4 { ledger[r][j] = ledger[r][j].sub(f.mul(rowop[j])); }
        }
        pivots.push(col);
        if pivots.len() == 4 { break; }
    }
    let schur_rank = pivots.len();
    let incompatible: Vec<usize> = (schur_rank..4).filter(|&r| schur[r][variables] != M31::ZERO).collect();
    if let Some(&bad) = incompatible.first() {
        let coeff = &ledger[bad];
        for j in 0..variables { assert_eq!((0..4).fold(M31::ZERO, |a, i| a.add(coeff[i].mul(schur_columns[j][i]))), M31::ZERO, "aggregate initial-claim left kernel {j}"); }
        let rhs = (0..4).fold(M31::ZERO, |a, i| a.add(coeff[i].mul(wanted[i])));
        assert_eq!(rhs, schur[bad][variables]); assert_ne!(rhs, M31::ZERO);
        println!("R117_C1_TOTAL_INITIAL_SCHUR rows=4 variables={variables} rank={schur_rank} incompatible_rows={} first_incompatible={:?}", incompatible.len(), incompatible.first());
        if let Some(path) = std::env::var_os("ASPIS_R117_C1_CERT_PATH") {
            let mut bytes = Vec::new();
            bytes.extend_from_slice(b"R117C1TOTALSCHUR1\0");
            bytes.extend_from_slice(&(16u32).to_le_bytes());
            for col in 0..16 {
                let width = rows_by_col[col].len();
                bytes.extend_from_slice(&(width as u32).to_le_bytes());
                bytes.extend_from_slice(&(pivots_by_col[col].len() as u32).to_le_bytes());
                for &p in &pivots_by_col[col] { bytes.extend_from_slice(&(p as u32).to_le_bytes()); }
                bytes.extend_from_slice(&(free_by_col[col].len() as u32).to_le_bytes());
                for &f in &free_by_col[col] { bytes.extend_from_slice(&(f as u32).to_le_bytes()); }
                for &r in &rows_by_col[col] { bytes.extend_from_slice(&(r as u32).to_le_bytes()); }
                for &x in &initial_covectors_by_col[col] { for limb in [x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0] { bytes.extend_from_slice(&limb.to_le_bytes()); } }
                for row in &matrices[col] { for x in row { bytes.extend_from_slice(&x.0.to_le_bytes()); } }
                for x in &targets[col] { bytes.extend_from_slice(&x.0.to_le_bytes()); }
                for x in &solutions[col] { bytes.extend_from_slice(&x.0.to_le_bytes()); }
            }
            bytes.extend_from_slice(&(variables as u32).to_le_bytes());
            for (col, free, direction) in &kernel_directions {
                bytes.extend_from_slice(&(*col as u32).to_le_bytes()); bytes.extend_from_slice(&(*free as u32).to_le_bytes());
                for x in direction { bytes.extend_from_slice(&x.0.to_le_bytes()); }
            }
            for row in 0..4 { for col in 0..variables { bytes.extend_from_slice(&schur_columns[col][row].0.to_le_bytes()); } }
            for x in wanted { bytes.extend_from_slice(&x.0.to_le_bytes()); }
            for x in coeff { bytes.extend_from_slice(&x.0.to_le_bytes()); }
            std::fs::write(path, &bytes).expect("write total initial-claim Schur certificate and kernel data");
        }
    }
    assert!(incompatible.is_empty(), "aggregate actual initial-mask claim incompatible with original C1 kernel choices");
    let mut schur_solution = vec![M31::ZERO; variables];
    for (r, &col) in pivots.iter().enumerate() { schur_solution[col] = schur[r][variables]; }
    for (j, (col, _free, direction)) in kernel_directions.iter().enumerate() {
        let amount = schur_solution[j];
        for (k, &row) in rows_by_col[*col].iter().enumerate() {
            let change = amount.mul(direction[k]);
            solutions[*col][k] = solutions[*col][k].add(change);
            result[*col][row] = result[*col][row].add(change);
            if map.inactive[row] { result[*col][1023] = result[*col][1023].sub(change); }
        }
    }

    for col in 0..16 {
        let _rows = &rows_by_col[col];
        for i in 0..108 { assert_eq!(dot_m31(&matrices[col][i], &solutions[col]), targets[col][i]); }
        let codeword = enc.encode_c1_message(&map.forward(&result[col])).unwrap();
        for &q in queries { for slot in 0..4 { assert_eq!(codeword[4 * q as usize + slot], M31::ZERO); } }
        let wide: Vec<_> = result[col].iter().map(|&v| K::from_cm31(CM31::from_m31(v))).collect();
        for p in corelib::v6_transcript::v6_statement_points(z) { assert_eq!(multilinear_evaluate_qm31(&wide, &p).unwrap(), K::ZERO); }
        for p in points { assert_eq!(ood(&wide, p), K::ZERO); }
        assert_eq!(result[col].iter().enumerate().filter(|(i, _)| map.inactive[*i]).fold(M31::ZERO, |a, (_, &v)| a.add(v)), M31::ZERO);
    }
    let final_initial_delta = (0..16).fold(K::ZERO, |sum, col| {
        sum.add(initial_covectors_by_col[col].iter().zip(&result[col]).fold(K::ZERO, |a, (&w, &v)| a.add(w.mul_m31(v))))
    });
    assert_eq!(final_initial_delta, K::ZERO, "actual aggregate source initial mask claim preserved");
    assert!(changed > 0, "genuine witness offset required");
    println!("R17_C1_WITNESS_CORRECTION columns=16 original_rows108=true aggregate_initial_claim_preserved=true schur_rank={schur_rank} schur_variables={variables} selected_raw_zeros=1408 point_claim_zeros=48 ood_claim_zeros=32 base_field_masks=true internal_vectors_not_serialized=true");
    result
}

// Read-only R550 export of the selected R19/G coefficient system. This builds
// the same 626 rows used by r17_g_witness_audit, but has no RHS and computes no
// witness correction.
fn r550_g_observation_matrix(
    z: &[K; 10], p: &Prefix, kappa: K, alpha: K, beta: K, queries: &[u32],
) -> Vec<Vec<K>> {
    use r17_coupled_audit::{chord, dot, eval_weights, qvector};
    let map = crate::r16_basis_transport::transport();
    let gw = crate::opening_weights::quotient_weights(z, kappa, p.abc, p.tau, true);
    let rw = crate::opening_weights::quotient_weights(z, kappa, p.abc, p.tau, false);
    let wr: Vec<_> = (0..1024).map(|i| rw.weight_at(i)).collect();
    let wg: Vec<_> = (0..1024).map(|i| gw.weight_at(i)).collect();
    let dw: Vec<_> = wg.iter().zip(&wr).map(|(&g, &r)| g.sub(r)).collect();
    let mut wb = WeightAccumulator::empty(10);
    wb.add_dense(wr.iter().zip(&wg).map(|(&r, &g)| crate::r19_channel_fold::lerp(r, g, beta)).collect()).unwrap();
    let pts = corelib::circle_fri::selected_circle_fiber_points_shared(20, queries).unwrap();
    let raw: Vec<_> = pts.iter().flat_map(|pt| [
        (pt.x, pt.y), (pt.x, pt.y.neg()), (pt.x.neg(), pt.y.neg()), (pt.x.neg(), pt.y),
    ]).map(|(x, y)| eval_weights(
        K::from_cm31(CM31::from_m31(x)), K::from_cm31(CM31::from_m31(y)),
    )).collect();
    assert_eq!(raw.len(), 88, "22 query points × 4 raw circle values");
    let mut point: Vec<Vec<K>> = corelib::v6_transcript::v6_statement_points(z).iter().map(|z| {
        let mut w = WeightAccumulator::empty(10);
        w.add_multilinear(K::ONE, z.to_vec()).unwrap();
        (0..1024).map(|i| w.weight_at(i)).collect()
    }).collect();
    point[0] = crate::structured_g::mask_weights(z);
    let mixing: Vec<_> = (0..271).map(crate::structured_g::mixing_row).collect();
    let mut matrix = vec![vec![K::ZERO; 1022]; 626];
    for j in 0..1022 {
        let mut unit = vec![K::ZERO; 1022]; unit[j] = K::ONE;
        let q = qvector(&unit, p.abc);
        let c = chord(&q, p.abc);
        let m = map.inverse(&c);
        for i in 0..271 { matrix[i][j] = dot(&mixing[i], &m); }
        for i in 0..88 { matrix[271 + i][j] = dot(&raw[i], &c); }
        for i in 0..3 { matrix[359 + i][j] = dot(&point[i], &m); }
        let f = primal(&q, alpha);
        for i in 0..256 { matrix[362 + i][j] = f[i]; }
        matrix[618][j] = (0..1024).filter(|&r| map.inactive[r]).fold(K::ZERO, |s, r| s.add(m[r]));
        matrix[625][j] = dot(&dw, &q);
        let poly = corelib::sumcheck::polynomial_for_extension(&q, &wb).map(|x| beta.mul(x));
        for (i, k) in [0, 1, 2, 3, 5, 6].into_iter().enumerate() { matrix[619 + i][j] = poly[k]; }
    }
    matrix
}

fn r550_write_matrix_certificate(
    directory: &str, matrix: &[Vec<K>], rref: &[Vec<K>], ledger: &[Vec<K>], pivots: &[usize],
) {
    let write_rows = |name: &str, rows: &[Vec<K>]| {
        let mut data = Vec::with_capacity(rows.len() * rows[0].len() * 16);
        for row in rows { data.extend(bytes(row)); }
        std::fs::write(format!("{directory}/{name}.bin"), data).unwrap();
    };
    write_rows("original-matrix", matrix);
    write_rows("coefficient-rref", rref);
    write_rows("row-ledger", ledger);
    let mut pivot_bytes = Vec::with_capacity(pivots.len() * 4);
    for &pivot in pivots { pivot_bytes.extend_from_slice(&(pivot as u32).to_le_bytes()); }
    std::fs::write(format!("{directory}/pivot-columns.u32le"), pivot_bytes).unwrap();
}


fn r550_reduce_g_matrix(matrix: &[Vec<K>]) -> (Vec<Vec<K>>, Vec<Vec<K>>, Vec<usize>) {
    let rows = matrix.len();
    let cols = matrix[0].len();
    assert_eq!((rows, cols), (626, 1022));
    let mut rref = matrix.to_vec();
    let mut ledger = vec![vec![K::ZERO; rows]; rows];
    for i in 0..rows { ledger[i][i] = K::ONE; }
    let mut pivots = Vec::new();
    for col in 0..cols {
        let r = pivots.len();
        let Some(pivot_row) = (r..rows).find(|&i| rref[i][col] != K::ZERO) else { continue; };
        rref.swap(r, pivot_row);
        ledger.swap(r, pivot_row);
        let inv = rref[r][col].inv();
        for x in &mut rref[r][col..] { *x = x.mul(inv); }
        for x in &mut ledger[r] { *x = x.mul(inv); }
        let normalized = rref[r].clone();
        let rowops = ledger[r].clone();
        for i in 0..rows {
            if i == r { continue; }
            let factor = rref[i][col];
            if factor == K::ZERO { continue; }
            for j in col..cols { rref[i][j] = rref[i][j].sub(factor.mul(normalized[j])); }
            for j in 0..rows { ledger[i][j] = ledger[i][j].sub(factor.mul(rowops[j])); }
        }
        pivots.push(col);
        if pivots.len() == rows { break; }
    }
    let rank = pivots.len();
    assert!(rref[rank..].iter().all(|row| row.iter().all(|&x| x == K::ZERO)), "all nonpivot coefficient rows are zero");
    for i in 0..rows {
        for j in 0..cols {
            let image = (0..rows).fold(K::ZERO, |acc, k| acc.add(ledger[i][k].mul(matrix[k][j])));
            assert_eq!(image, rref[i][j], "row ledger reproduces coefficient RREF at ({i},{j})");
        }
    }
    (rref, ledger, pivots)
}
