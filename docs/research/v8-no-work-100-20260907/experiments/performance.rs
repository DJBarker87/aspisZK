//! Synthetic honest payment performance only. No extractor, corruption search,
//! full-domain diagnostic, or claim of a complete pool transaction.
use super::*;
use std::time::Instant;
fn phase(seed:u8,name:&str,t:Instant){println!("PERF {{\"seed\":{seed},\"phase\":\"{name}\",\"seconds\":{}}}",t.elapsed().as_secs_f64());}
pub fn run(){
    #[cfg(v8_gamma_wrap)] super::super::query_arithmetic::controls();
    #[cfg(v8_structured)] {
        row::structured::controls();
        if std::env::args().nth(1).as_deref()==Some("--structured-controls"){return;}
        if std::env::args().nth(1).as_deref()==Some("--verify-existing"){
            let dir=std::env::args().nth(2).expect("fixture directory");
            let public=std::fs::read(format!("{dir}/public.bin")).unwrap();
            let transition=std::fs::read(format!("{dir}/transition.bin")).unwrap();
            let binding:[u8;32]=std::fs::read(format!("{dir}/binding.bin")).unwrap().try_into().unwrap();
            for seed in [1,2,3]{
                let body=std::fs::read(format!("{dir}/proof-{seed}.bin")).unwrap();
                assert_eq!(super::super::performance_verifier::verify(&body,&binding,&public,&transition),Ok(()));
                for index in [0,HEAD,body.len()-1,417*16,441*16]{
                    let mut bad=body.clone();bad[index]^=1;
                    assert!(super::super::performance_verifier::verify(&bad,&binding,&public,&transition).is_err());
                }
                let mut bad=body.clone();bad[..4].copy_from_slice(&corelib::field::P.to_le_bytes());
                assert!(super::super::performance_verifier::verify(&bad,&binding,&public,&transition).is_err());
                assert!(super::super::performance_verifier::verify(&body[..body.len()-1],&binding,&public,&transition).is_err());
            }
            println!("STRUCTURED_EXISTING three_honest=true seven_negative_cases_per_seed=true dense_v2_outcomes=true");return;
        }
    }
    #[cfg(v8_performance_fast)] row::performance_controls();
    let out=std::env::args().nth(1).expect("new output directory required");
    std::fs::create_dir(&out).expect("output directory must not exist");
    let setup=Instant::now();
    let(public,witness,snapshot)=we::fixture();
    let authoritative=PoolV1PaymentRelationContextV1{runtime_binding:provision_accounts(&witness),spent_nullifiers:&[]};
    let compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,&witness,authoritative,snapshot).unwrap();
    let transition=compiled.public_statement;
    let enc=CircleEncoder::new_for_domain_log(20);
    // Public matrix is a prover quotient-interpolation aid, NOT an extractor.
    let decoder=ac::Decoder::new(&enc);
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&(0..256).collect::<Vec<_>>()).unwrap();
    phase(0,"setup_compiler_encoder_matrix",setup);
    let public_bytes=encode_pool_v1_private_transfer_public_v1(&public).unwrap();
    let mut transition_bytes=vec![0;POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES];
    encode_pool_v1_pair_late_public_statement_v1(&transition,&mut transition_bytes).unwrap();
    std::fs::write(format!("{out}/public.bin"),&public_bytes).unwrap();
    std::fs::write(format!("{out}/transition.bin"),&transition_bytes).unwrap();
    let binding=hash(&[b"AV8 synthetic account fixture",&public_bytes,format!("{transition:?}").as_bytes()]);
    std::fs::write(format!("{out}/binding.bin"),binding).unwrap();
    for seed in [1u8,2,3] {
        let total=Instant::now();let clock=Instant::now();
        let hc=StateOnlyHidingContext::pool_v1_pair_forest_v1(binding,[seed;32]);
        let attempt=state_only_entropy::StateOnlyAttemptSecrets::deterministic_spend_fixture([seed;32],[seed+1;32],[seed+2;32]);
        let(reserved,material)=attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,binding,hc,&mut InMemoryStateOnlyMaskNonceStore::default()).unwrap();
        let d=reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,hc).unwrap();
        let mut trace=compiled.semantic_c1.clone();
        let masks=apply_pool_v1_pair_forest_mask_material_v1(&mut trace,material).unwrap();
        let selected:Vec<Vec<M31>>=trace.c1.iter().chain(masks.mask_only_c1.iter()).cloned().collect();
        phase(seed,"masking",clock);let clock=Instant::now();
        let encoded:Vec<Vec<M31>>=selected.iter().map(|m|enc.encode_c1_message(m).unwrap()).collect();
        phase(seed,"c1_encode",clock);let clock=Instant::now();
        let salts:Vec<[u8;32]>=(0..N/4).map(|i|reserved.derive_pool_v1_leaf_salt(hash,hc,0x77,i as u32).unwrap()).collect();
        let a=tree((0..N/4).map(|i|private_leaf_hash_v7(hash,V7_C1_TREE_TAG,&c1leaf(&encoded,i),&salts[i])).collect());
        phase(seed,"c1_salts_pack_tree",clock);let clock=Instant::now();
        let(t,lambda,chi)=start(&binding,&a);
        let mut h=aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(
            &compiled.trace,snapshot.next_pair_index,lambda,chi).unwrap();
        apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h,&masks.h1_padding).unwrap();
        let c2=vec![h,masks.g.clone(),d];
        let c2encoded:Vec<Vec<K>>=c2.iter().map(|m|enc.encode_c2_message(m).unwrap()).collect();
        let messages:Vec<Vec<K>>=selected.iter().map(|c|c.iter().map(|v|K::from_cm31(CM31::from_m31(*v))).collect()).chain(c2.iter().cloned()).collect();
        let initial=state_only_initial_mask_claim(&trace,&masks.mask_only_c1,&masks.g).unwrap();
        phase(seed,"c2_helpers_encode",clock);let clock=Instant::now();
        let b=tree((0..N/4).map(|i|private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&c2leaf(&c2encoded,i,false),&salts[i])).collect());
        phase(seed,"c2_pack_tree",clock);let clock=Instant::now();
        let mut v=vec![K::ZERO;697];v[0]=initial;
        let mut s=semantic_produce(&mut v,semantic_start(t.clone(),&b,initial,lambda,chi),&public,&transition,&messages);
        v[271..358].copy_from_slice(&point_rows(&messages,&s.z));
        phase(seed,"semantic_producer_literal",clock);let clock=Instant::now();
        let empty=vec![0;Q*REC];let stub=f::body(&v,&a,&b,&empty,(&[],&[]));let w=parse(&stub).unwrap();
        row::points_absorb(&mut s.t,&w);
        let p0=s.t.challenge_secure_circle_point().unwrap();
        for j in 0..29{v[359+j]=ood(&messages[j],p0);}
        let mut rec=vec![0];rec.extend(bytes(&v[359..388]));s.t.absorb(V8_COMPONENT_OOD_VECTOR,&rec);
        let p1=(0..3).map(|_|s.t.challenge_secure_circle_point().unwrap()).find(|p|*p!=p0).unwrap();
        for j in 0..29{v[388+j]=ood(&messages[j],p1);}
        let mut rec=vec![1];rec.extend(bytes(&v[388..417]));s.t.absorb(V8_COMPONENT_OOD_VECTOR,&rec);
        s.t.absorb(label::M31_PAYMENT_BATCH_POW_NONCE,&[0;8]);
        let gamma=sample(&mut s.t,true).unwrap();
        let mut iw=WeightAccumulator::empty(10);
        iw.add_grouped_64x16_binary_masks_deferred_prepared(pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1(),pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1()).unwrap();
        let combined:Vec<K>=(0..1024).map(|i|messages.iter().rev().fold(K::ZERO,|x,m|x.mul(gamma).add(m[i]))).collect();
        v[358]=(0..1024).fold(K::ZERO,|sum,i|sum.add(iw.weight_at(i).mul(combined[i as usize])));
        let stub=f::body(&v,&a,&b,&empty,(&[],&[]));let w=parse(&stub).unwrap();
        let sem=semantic_replay(&w,&public,&transition,semantic_start(t.clone(),&b,initial,lambda,chi));
        let(mut p,ordinary,mut claim,_)=row::prepare(sem,&w,true).unwrap();
        let mut qeval=Vec::new();
        for(i,pt)in pts.iter().enumerate(){for(slot,(x,y))in[(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate(){
            let value=(0..29).rev().fold(K::ZERO,|acc,col|acc.mul(gamma).add(if col<26{K::from_cm31(CM31::from_m31(encoded[col][4*i+slot]))}else{c2encoded[col-26][4*i+slot]}));
            let l=p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y));
            qeval.push(value.sub(p.iv[0].add(p.iv[1].mul_m31(if p.use_x{x}else{y}))).mul(l.try_inv().unwrap()));
        }}
        let q=decoder.solve_wide(&qeval);
        assert_eq!(q[1023],K::ZERO);assert_eq!(p.abc[1].mul(q[1022]).sub(p.abc[2].mul(q[1021])),K::ZERO);
        assert_eq!(claim,dot(&ordinary,&q));
        phase(seed,"ood_transpose_quotient",clock);let clock=Instant::now();
        let mut weights=WeightAccumulator::empty(10);weights.add_dense(ordinary).unwrap();
        let mut image=vec![K::ZERO;1024];image[1023]=p.tau;image[1022]=p.tau.square().mul(p.abc[1]);image[1021]=p.tau.square().mul(p.abc[2]).neg();weights.add_dense(image).unwrap();
        f::save_round(&mut v,0,polynomial_for_extension(&q,&weights));
        let first=compact(&v[417..423],claim);absorb_round(&mut p.t,0,&first);
        p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&[0;9]);
        let alpha=sample(&mut p.t,false).unwrap();claim=evaluate(&first,alpha);weights.fold_deferred_relation_arity4(alpha);
        let mut finals=primal(&q,alpha);v[441..697].copy_from_slice(&finals);
        let(queries,rho)=query_schedule(&mut p,&finals,&[0;24]).unwrap();
        let records:Vec<u8>=queries.iter().flat_map(|&id|{let i=id as usize;let mut r=c1leaf(&encoded,i);r.extend(c2leaf(&c2encoded,i,false));r.extend(salts[i]);r}).collect();
        let fa=f::frontier(&a,&queries);let fb=f::frontier(&b,&queries);
        let stub=f::body(&v,&a,&b,&records,(&fa,&fb));let w=parse(&stub).unwrap();
        let(values,xs)=opened_values(&w,&p,&queries,alpha,hash).unwrap();
        let inc=inject(&mut weights,&mut claim,&values,&xs,rho).unwrap();p.t.absorb(label::PROFILE,&bytes(&[inc]));
        for r in 1..4{f::save_round(&mut v,r,polynomial_for_extension(&finals,&weights));let poly=compact(&v[417+6*r..423+6*r],claim);
            absorb_round(&mut p.t,r,&poly);let a=sample(&mut p.t,false).unwrap();claim=evaluate(&poly,a);weights.fold_deferred_relation_arity4(a);finals=primal(&finals,a);}
        let body=f::body(&v,&a,&b,&records,(&fa,&fb));
        phase(seed,"relation_openings_serialize",clock);
        phase(seed,"prover_total_excludes_setup",total);
        // Verifier starts from bytes and public inputs; no witness/anchor.
        let clock=Instant::now();
        assert_eq!(super::super::performance_verifier::verify(&body,&binding,&public_bytes,&transition_bytes),Ok(()));
        phase(seed,"host_verify_from_public_bytes",clock);
        for index in [0,HEAD,body.len()-1] {
            let mut bad=body.clone();bad[index]^=1;
            assert!(super::super::performance_verifier::verify(&bad,&binding,&public_bytes,&transition_bytes).is_err());
        }
        assert!(super::super::performance_verifier::verify(&body[..body.len()-1],&binding,&public_bytes,&transition_bytes).is_err());
        std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();
        println!("PERF {{\"seed\":{seed},\"accepted\":true,\"body_bytes\":{},\"max_body_bytes\":40282,\"grinding_attempts\":0,\"full_transaction_cu\":null}}",body.len());
    }
}
