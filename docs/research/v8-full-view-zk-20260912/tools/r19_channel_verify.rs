// New-profile verifier suffix. No claim of source extraction or privacy.
pub(super) fn channel_challenge(p:&mut Prefix,claim:K,sent:[K;2])->Result<(K,K),Error>{
    p.t.absorb(label::PROFILE,b"AV8/R19/channel-polynomial/p0-p2/v1");
    p.t.absorb(label::CLAIM,&bytes(&sent));
    p.t.absorb(label::PROFILE,b"AV8/R19/channel-beta/v1");
    let beta=sample(&mut p.t,false)?;
    Ok((beta,crate::r19_channel_fold::evaluate(claim,sent,beta)))
}

pub(super) fn verify(w:&Wire<'_>,prepared:Prepared,reference:bool)->Result<(),Error>{
    let Prepared{public_audit,mut p,iv_g,mut weights,claim:incoming}=prepared;
    let (beta,mut claim)=channel_challenge(&mut p,incoming,[w.v[417],w.v[418]])?;
    let mut dense=if reference {(0..1024).map(|i|crate::r19_channel_fold::lerp(
        weights[0].weight_at(i),weights[1].weight_at(i),beta)).collect::<Vec<_>>()}else{vec![]};
    let mut workspace=if reference {vec![]}else{
        core::mem::replace(&mut weights[0],WeightAccumulator::empty(10))
            .into_single_dense_for_workspace().ok_or(Error::Shape)?};
    let mut query=WeightAccumulator::empty(8);
    let first=compact(&w.v[419..425],claim);absorb_round(&mut p.t,0,&first);
    let mut work=vec![0];work.extend_from_slice(&w.nonces[8..16]);
    p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&work);
    let a=sample(&mut p.t,false)?;claim=evaluate(&first,a);
    let mut alphas=[a,K::ZERO,K::ZERO,K::ZERO];
    if reference {dense=fold_dense(&dense,a);}
    let mut finals=w.v[443..699].to_vec();
    let (queries,rho)=query_schedule(&mut p,&finals,w.nonces)?;
    #[cfg(target_os="solana")] {solana_program::msg!("R19:query-schedule-end");solana_program::log::sol_log_compute_units();}
    let (values,xs)=opened_channel(w,&p,iv_g,&queries,a,beta)?;
    #[cfg(target_os="solana")] {solana_program::msg!("R19:openings-end");solana_program::log::sol_log_compute_units();}
    let inc=if reference {
        let mut power=rho;let mut inc=K::ZERO;
        for i in 0..Q {inc=inc.add(power.mul(values[i]));
            for j in 0..256 {let mut unit=vec![K::ZERO;256];unit[j]=K::ONE;
                dense[j]=dense[j].add(power.mul(corelib::v6_onefold::evaluate_final256_coefficients(&unit,xs[i]).map_err(|_|Error::Shape)?));}
            power=power.mul(rho);
        }
        claim=claim.add(inc);inc
    }else{inject(&mut query,&mut claim,&values,&xs,rho)?};
    p.t.absorb(label::PROFILE,&bytes(&[inc]));
    for r in 1..4 {
        let poly=compact(&w.v[419+6*r..425+6*r],claim);absorb_round(&mut p.t,r,&poly);
        let a=sample(&mut p.t,false)?;alphas[r]=a;claim=evaluate(&poly,a);
        finals=owned_primal::fold(finals,a);
        if reference{dense=fold_dense(&dense,a)}else{query.fold_deferred_relation_arity4(a)}
    }
    #[cfg(target_os="solana")] {solana_program::msg!("R19:tail-folds-end");solana_program::log::sol_log_compute_units();}
    let mut terminal=corelib::field::qm31_sum_products4(
        if reference {core::array::from_fn(|i|dense[i])}else{query.weight_prefix::<4>()},
        core::array::from_fn(|i|finals[i]));
    if !reference {
        let ordinary=crate::r19_channel_ordinary::terminal(&public_audit,p.abc,alphas,beta,&mut workspace);
        #[cfg(target_os="solana")] {solana_program::msg!("R19:ordinary-end");solana_program::log::sol_log_compute_units();}
        let z=core::array::from_fn(|i|public_audit[i]);
        let sparse=crate::r18_compact_g::terminal(&z,p.abc,alphas,&mut workspace);
        terminal=terminal.add(corelib::field::qm31_sum_products4(
            core::array::from_fn(|i|ordinary[i].add(beta.mul(public_audit[10]).mul(sparse[i]))),
            core::array::from_fn(|i|finals[i])));
        // i1=tau*i0 exactly; retains arbitrary image residuals, including beta0/1.
        let image_scale=K::ONE.sub(beta).add(beta.mul(p.tau.square()));
        terminal=terminal.add(image_scale.mul(image_terminal(p.tau,p.abc[1],p.abc[2],alphas)).mul(finals[3]));
    }
    if terminal!=claim{return Err(Error::Terminal)}
    #[cfg(target_os="solana")] {solana_program::msg!("R19:primary-terminal-accepted");solana_program::log::sol_log_compute_units();}
    if !reference && std::env::args().nth(1).as_deref()==Some("--audit-existing") {
        let mut fields=public_audit.to_vec();fields.extend([p.tau,a,p.points[0].x,p.points[0].y,p.points[1].x,p.points[1].y,p.gamma,beta,w.v[417],w.v[418]]);
        eprintln!("R19_PUBLIC_PREFIX {{\"fields\":{:?},\"queries\":{:?}}}",bytes(&fields),queries);
    }
    Ok(())
}
