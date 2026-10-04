//! Synthetic honest payment performance only. No extractor, corruption search,
//! full-domain diagnostic, or claim of a complete pool transaction.
use super::*;
#[path="../../v8-positive-complete-devnet-20260909/live_context.rs"] mod live_context;
use std::time::Instant;
#[path="complete_binding.rs"] mod complete_binding;
fn phase(seed:u8,name:&str,t:Instant){println!("PERF {{\"seed\":{seed},\"phase\":\"{name}\",\"seconds\":{}}}",t.elapsed().as_secs_f64());}
// Stress-fixture generation only: use the existing last nonce to seek the
// MAXIMUM authentication frontier. No security credit; no verifier change.
// The cap is explicit, failure is reported, and all earlier commitments/final
// coefficients remain fixed. This is NOT the ordinary prover timing mode.
fn stress_queries(p:&mut Prefix,finals:&[K])->(Vec<u32>,K,[u8;24],u64){
    let mut nonce=[0u8;24];
    let Some(cap)=std::env::var("ASPIS_V8_MAX_FRONTIER_SCAN").ok() else{
        let(q,rho)=query_schedule(p,finals,&nonce).unwrap();return(q,rho,nonce,0);
    };
    let cap:u64=cap.parse().unwrap();assert!(cap>0&&cap<=1_000_000);
    let clock=Instant::now();let prefix=p.t.clone();
    for attempt in 0..cap {
        nonce[16..24].copy_from_slice(&attempt.to_le_bytes());p.t=prefix.clone();
        let Ok((q,rho))=query_schedule(p,finals,&nonce) else{continue;};
        let mut nodes=q.clone();nodes.sort_unstable();
        let mut frontier=0;
        for _ in 0..18 {
            for &j in &nodes {if nodes.binary_search(&(j^1)).is_err(){frontier+=1;}}
            for j in &mut nodes{*j>>=1;}nodes.dedup();
        }
        if frontier==296 {
            println!("STRESS {{\"attempts\":{},\"seconds\":{},\"frontier_each\":296,\"security_credit_bits\":0}}",attempt+1,clock.elapsed().as_secs_f64());
            return(q,rho,nonce,attempt+1);
        }
    }
    panic!("maximum-frontier stress scan exhausted its declared cap");
}
pub fn run(){
    if std::env::args().nth(1).as_deref()==Some("--audit-existing"){
        let dir=std::env::args().nth(2).unwrap();
        let public=std::fs::read(format!("{dir}/public.bin")).unwrap();
        let transition=std::fs::read(format!("{dir}/transition.bin")).unwrap();
        let binding:[u8;32]=std::fs::read(format!("{dir}/binding.bin")).unwrap().try_into().unwrap();
        let body=std::fs::read(format!("{dir}/proof-1.bin")).unwrap();
        assert_eq!(super::super::performance_verifier::verify(&body,&binding,&public,&transition),Ok(()));
        println!("R17_PUBLIC_PREFIX_ACCEPTED");return;
    }
    if std::env::args().nth(1).as_deref()==Some("--reject-existing"){
        let dir=std::env::args().nth(2).unwrap();
        let public=std::fs::read(format!("{dir}/public.bin")).unwrap();
        let transition=std::fs::read(format!("{dir}/transition.bin")).unwrap();
        let binding:[u8;32]=std::fs::read(format!("{dir}/binding.bin")).unwrap().try_into().unwrap();
        let body=std::fs::read(format!("{dir}/proof-1.bin")).unwrap();
        assert!(super::super::performance_verifier::verify(&body,&binding,&public,&transition).is_err());
        println!("R17_LEGACY_PROFILE_REJECTED");return;
    }

    #[cfg(v8_positive_transfer)] super::super::positive_transfer::layout_control();
    #[cfg(v8_early_prefix)] super::super::early_c1_trace::begin();
    #[cfg(v8_gamma_wrap)] super::super::query_arithmetic::controls();
    #[cfg(v8_gamma_wrap)]
    if std::env::args().nth(1).as_deref()==Some("--gamma-controls"){return;}
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
    #[cfg(v8_semantic_rejoin)] std::env::set_var("ASPIS_SEMANTIC_REJOIN_OUTPUT",&out);
    let setup=Instant::now();
    let(public,witness,mut snapshot)=if std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_some(){live_context::load()}else{we::fixture()};
    let mut payment=PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public);
    let mut runtime=provision_accounts(&witness);
    if std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_some(){assert_eq!(runtime.anchor_root,public.anchor_root);runtime.pool=public.pool;runtime.deployment_domain=public.deployment_domain;runtime.anchor_sequence=public.anchor_sequence;}
    let mut complete_context=std::env::var("ASPIS_V8_COMPLETE_CONTEXT").ok().map(|directory| {
        let statement_bytes:[u8;POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES]=std::fs::read(format!("{directory}/statement.bin")).unwrap().try_into().unwrap();
        let statement=decode_pool_v1_pair_forest_terminal_statement_v1(&statement_bytes).unwrap();
        validate_pool_v1_pair_forest_terminal_statement_v1(&statement).unwrap();
        let (root,asset,sequence)=match &statement {
            PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>{payment=PoolV1PairForestTerminalPaymentV1::PrivateTransfer(*public);(public.anchor_root,public.asset_id,public.anchor_sequence)},
            PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>{payment=PoolV1PairForestTerminalPaymentV1::Withdrawal(*public);(public.anchor_root,public.asset_id,public.anchor_sequence)},
        };
        // Account context was exported by the actual combined harness BEFORE
        // proof creation; retain the independent input-tree/root assertions.
        assert_eq!(root,runtime.anchor_root);
        assert_eq!(asset,runtime.asset_id);
        assert_eq!(sequence,runtime.anchor_sequence);
        snapshot=statement.common().lane_transition.live_snapshot;
        runtime.pool=statement.common().master_account;
        runtime.deployment_domain=snapshot.deployment_domain;
        let verifier:[u8;32]=std::fs::read(format!("{directory}/verifier.bin")).unwrap().try_into().unwrap();
        let proof:[u8;32]=std::fs::read(format!("{directory}/proof-account.bin")).unwrap().try_into().unwrap();
        assert_eq!(V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,complete_binding::V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,"research profile cfg required");
        let digest=v7_pool_pair_forest_tag73_statement_digest_v1(&statement_bytes,hash);
        (statement,complete_binding::bind_attempt(hash,&digest,&verifier,&proof))
    });
    let authoritative=PoolV1PaymentRelationContextV1{runtime_binding:runtime,spent_nullifiers:&[]};
    let compiled=match &payment {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)=>compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(public,&witness,authoritative,snapshot),
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public)=>{
            let dig=|seed:u32|std::array::from_fn(|i|M31(seed+17*i as u32+1));
            let w=PoolV1PairForestWithdrawalWitnessV1{input:witness.input,change:PoolV1OutputNoteWitnessV1{owner_key:dig(700),salt:dig(800),value:750}};
            compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(public,&w,authoritative,snapshot)
        }
    }.unwrap();
    #[cfg(v8_positive_transfer)] let positive_case=std::env::var("ASPIS_V8_POSITIVE_CASE").unwrap_or_else(|_|"honest".into());
    #[cfg(v8_semantic_rejoin)] assert_eq!(positive_case,"recipient_zero","diagnostic requires the predeclared recipient_zero fixture");
    #[cfg(v8_positive_transfer)] let compiled={
        assert!(matches!(payment,PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)),"transfer-only profile");
        let p=match payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p,_=>panic!("transfer-only")};
        let(p,c)=super::super::positive_transfer::case_compilation(&positive_case,&compiled,p,witness);
        payment=PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p);c
    };
    let alternate=if std::env::var_os("ASPIS_R17_C1_WITNESS_AUDIT").is_some(){
            assert!(std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_none());
            assert!(std::env::var_os("ASPIS_V8_COMPLETE_CONTEXT").is_none());
            assert_eq!(positive_case,"honest");
            let mut other=witness;other.input.pair.selected_second=!other.input.pair.selected_second;
            let public=match payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p,_=>panic!("fixture transfer only")};
            let other_compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,&other,authoritative,snapshot).unwrap();
            assert_eq!(other_compiled.public_statement,compiled.public_statement);
            Some((other,other_compiled))
        }else{None};
        let transition=compiled.public_statement;
    #[cfg(v8_positive_transfer)] if let Some((statement,attempt))=&mut complete_context {
        let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=payment else{panic!("transfer only")};
        let mut common=*statement.common();common.lane_transition=transition;
        *statement=PoolV1PairForestTerminalStatementV1::PrivateTransfer{public:p,common};
        let sb=encode_pool_v1_pair_forest_terminal_statement_v1(statement).unwrap();
        let digest=v7_pool_pair_forest_tag73_statement_digest_v1(&sb,hash);
        let dir=std::env::var("ASPIS_V8_COMPLETE_CONTEXT").unwrap();
        let vk:[u8;32]=std::fs::read(format!("{dir}/verifier.bin")).unwrap().try_into().unwrap();
        let pk:[u8;32]=std::fs::read(format!("{dir}/proof-account.bin")).unwrap().try_into().unwrap();
        *attempt=complete_binding::bind_attempt(hash,&digest,&vk,&pk);
        std::fs::write(format!("{out}/statement.bin"),sb).unwrap();
    }
    if let Some((statement,_))=&complete_context{assert_eq!(transition,statement.common().lane_transition);}
    let enc=CircleEncoder::new_for_domain_log(20);
    // Public matrix is a prover quotient-interpolation aid, NOT an extractor.
    let decoder=ac::Decoder::new(&enc);
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&(0..256).collect::<Vec<_>>()).unwrap();
    phase(0,"setup_compiler_encoder_matrix",setup);
    let public_bytes=match &payment {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>encode_pool_v1_private_transfer_public_v1(p).unwrap().to_vec(),
        PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>encode_pool_v1_withdrawal_public_v1(p).unwrap().to_vec(),
    };
    let mut transition_bytes=vec![0;POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES];
    encode_pool_v1_pair_late_public_statement_v1(&transition,&mut transition_bytes).unwrap();
    #[cfg(v8_semantic_rejoin)] {
        let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(selected_public)=payment else { panic!("transfer-only diagnostic"); };
        let decoded_public=decode_pool_v1_private_transfer_public_v1(&public_bytes)
            .expect("selected raw public decoder accepts rewritten recipient_zero statement");
        validate_pool_v1_private_transfer_public_v1(&decoded_public)
            .expect("selected typed public validator accepts rewritten statement");
        assert_eq!(decoded_public,selected_public);
        let decoded_transition=decode_pool_v1_pair_late_public_statement_v1(&transition_bytes)
            .expect("selected raw transition decoder accepts recipient_zero transition");
        assert_eq!(decoded_transition,transition);
        println!("ZERO_OUTPUT_SETUP raw_public_decode=ok typed_public_validate=ok raw_transition_decode=ok before_oracle_arm=true");
    }
    std::fs::write(format!("{out}/public.bin"),&public_bytes).unwrap();
    std::fs::write(format!("{out}/transition.bin"),&transition_bytes).unwrap();
    let binding=complete_context.as_ref().map(|(_,b)|*b).unwrap_or_else(||hash(&[b"AV8 synthetic account fixture",&public_bytes,format!("{transition:?}").as_bytes()]));
    std::fs::write(format!("{out}/binding.bin"),binding).unwrap();
    #[cfg(v8_semantic_rejoin)] let seeds=[1u8]; // fixed one-seed diagnostic; no retries/search
    #[cfg(all(not(v8_semantic_rejoin),any(v8_early_prefix,v8_positive_transfer)))] let seeds=[1u8]; // one predeclared trace; no nonce search
    #[cfg(all(not(v8_semantic_rejoin),not(any(v8_early_prefix,v8_positive_transfer))))] let seeds=[1u8,2,3];
    #[cfg(v8_early_prefix)] assert!(std::env::var_os("ASPIS_V8_MAX_FRONTIER_SCAN").is_none());
    assert!(std::env::var_os("ASPIS_V8_MAX_FRONTIER_SCAN").is_none());
    for seed in seeds {
        let total=Instant::now();let clock=Instant::now();
        let hc=StateOnlyHidingContext::pool_v1_pair_forest_v1(binding,[seed;32]);
        let attempt=state_only_entropy::StateOnlyAttemptSecrets::deterministic_spend_fixture([seed;32],[seed+1;32],[seed+2;32]);
        #[cfg(v8_positive_transfer)] let mask_binding=super::super::positive_transfer::entropy_binding(&binding);
        #[cfg(not(v8_positive_transfer))] let mask_binding=binding;
        let(reserved,material)=attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,mask_binding,hc,&mut InMemoryStateOnlyMaskNonceStore::default()).unwrap();
        let d=reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,hc).unwrap();
        let mut trace=compiled.semantic_c1.clone();
        let masks=apply_pool_v1_pair_forest_mask_material_v1(&mut trace,material).unwrap();
        #[cfg(v8_positive_transfer)] {
            let before=trace.clone();
            if positive_case=="honest"{super::super::positive_transfer::install(&mut trace).unwrap();}
            else {
                let install_result=super::super::positive_transfer::install(&mut trace);
                assert_eq!(install_result,Err(Error::Domain));
                #[cfg(v8_semantic_rejoin)] println!("ZERO_OUTPUT_SETUP private_install=Domain producer_bypassed_install=true");
                trace.c1[3][1014]=M31::ZERO; // malicious producer path only; verifier relation remains untouched
            }
            for col in 0..16{for r in 0..1024{if col!=3 || r!=1014{assert_eq!(trace.c1[col][r],before.c1[col][r]);}}}
            assert!(trace.c1.iter().flatten().all(|v|v.0<corelib::field::P));
            assert_eq!(we::decode(&trace),we::decode(&before));
            let checked_extractor_accepts=we::extract_checked(&trace,match &payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p,_=>panic!("transfer-only")},&transition,authoritative).is_ok();
            assert_eq!(checked_extractor_accepts,positive_case=="honest");
            #[cfg(v8_semantic_rejoin)] println!("ZERO_OUTPUT_SETUP checked_extractor_accepts={checked_extractor_accepts} public_transition_unchanged_after_setup=true");
            let active=pool_v1_pair_forest_copy_active_rows_v1().unwrap();
            for col in 0..16{assert_eq!((0..1024).filter(|r|!active.contains(&(*r as u16))).fold(M31::ZERO,|a,r|a.add(trace.c1[col][r])),M31::ZERO);}
        }
        #[cfg(v8_semantic_rejoin)] if positive_case=="honest" {
            let public=match &payment {PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p,_=>panic!("transfer-only selected verifier")};
            assert!(we::extract_checked(&trace,public,&transition,authoritative).is_ok(),"normal public installation/extraction must succeed before mutation");
            trace.c1[0][12]=trace.c1[0][12].add(M31::ONE);
            assert!(trace.c1.iter().flatten().all(|v|v.0<corelib::field::P),"mutated C1 remains canonical");
            assert!(we::extract_checked(&trace,public,&transition,authoritative).is_err(),"actual checked extractor must reject the changed trace");
            println!("SEMANTIC_REJOIN_SETUP public_install_ok=true changed_trace_extractor_rejects=true changed_cell=masked_c1_0_12 public_binding_transition_unchanged=true");
        }
        let selected:Vec<Vec<M31>>=trace.c1.iter().chain(masks.mask_only_c1.iter()).cloned().collect();
        phase(seed,"masking",clock);let clock=Instant::now();
        let encoded:Vec<Vec<M31>>=selected.iter().map(|m|enc.encode_c1_message(&crate::r16_basis_transport::transport().forward(m)).unwrap()).collect();
        phase(seed,"c1_encode",clock);let clock=Instant::now();
        let salts:Vec<[u8;32]>=(0..N/4).map(|i|reserved.derive_pool_v1_leaf_salt(hash,hc,0x77,i as u32).unwrap()).collect();
        let a=crate::r102_tree::tree(hash,(0..N/4).map(|i|private_leaf_hash_v7(hash,V7_C1_TREE_TAG,&c1leaf(&encoded,i),&salts[i])).collect());
        // Actual answers frozen before `start` samples lambda and chi. The
        // resolver receives neither the encoded columns nor their preimages
        // through any other channel, and never queries the hash oracle.
        #[cfg(v8_early_prefix)] let early_c1=super::super::early_c1_trace::Prefix::new(super::super::early_c1_trace::freeze()).unwrap();
        phase(seed,"c1_salts_pack_tree",clock);let clock=Instant::now();
        let(t,lambda,chi)=start(&binding,&a);
        let mut h=aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(
            &compiled.trace,snapshot.next_pair_index,lambda,chi).unwrap();
        apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h,&masks.h1_padding).unwrap();
        let c2=vec![h,masks.g.clone(),d];
        let c2encoded:Vec<Vec<K>>=c2.iter().map(|m|enc.encode_c2_message(&crate::r16_basis_transport::transport().forward(m)).unwrap()).collect();
        let messages:Vec<Vec<K>>=selected.iter().map(|c|c.iter().map(|v|K::from_cm31(CM31::from_m31(*v))).collect()).chain(c2.iter().cloned()).collect();
        let initial=crate::r17_relation::initial(state_only_initial_mask_claim(&trace,&masks.mask_only_c1,&masks.g).unwrap(),&masks.g);
        phase(seed,"c2_helpers_encode",clock);let clock=Instant::now();
        let b=crate::r102_tree::tree(hash,(0..N/4).map(|i|private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&c2leaf(&c2encoded,i,false),&salts[i])).collect());
        phase(seed,"c2_pack_tree",clock);let clock=Instant::now();
        let mut v=vec![K::ZERO;FIXED];v[0]=initial;
        #[cfg(all(v8_positive_transfer,not(v8_semantic_rejoin)))] if positive_case!="honest"{
            let s=semantic_negative_fixture(&mut v,semantic_start(t.clone(),&b,initial,lambda,chi),&payment,&transition,&messages);
            v[271..358].copy_from_slice(&point_rows(&messages,&s.z));
            // Well-shaped body with actual fixed roots/semantic responses and
            // point claims. Later PCS suffix is unconstructed, since the
            // actual verifier must reject at semantic error4, before PCS.
            let body=f::body(&v,&a,&b,&vec![0;Q*REC],(&[],&[]));
            assert!(parse(&body).is_ok());
            assert_eq!(super::super::performance_verifier::verify_payment(&body,&binding,&payment,&transition),Err(4));
            println!("POSITIVE_CASE case={} seed=1 actual_C1_C2_committed=true masked=true compact_rounds=10 verifier_error=4 verifier_reached_PCS=false nonce_search=false complete_bad_proof=false",positive_case);
            std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();
            continue;
        }
        #[cfg(v8_semantic_rejoin)] let mut s=semantic_negative_fixture(&mut v,semantic_start(t.clone(),&b,initial,lambda,chi),&payment,&transition,&messages);
        #[cfg(not(v8_semantic_rejoin))] let mut s=semantic_produce(&mut v,semantic_start(t.clone(),&b,initial,lambda,chi),&payment,&transition,&messages);
        let h1_coordinates=if std::env::var_os("ASPIS_R17_H1_SEMANTIC_AUDIT").is_some() || std::env::var_os("ASPIS_R17_COUPLED_AUDIT").is_some(){Some(r17_h1_semantic_audit(&payment,&transition,&messages,&s))}else{None};
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
        let sem=semantic_replay(&w,&payment,&transition,semantic_start(t.clone(),&b,initial,lambda,chi));

        let prepared=crate::r17_relation::prepare(sem,&w).unwrap();
        let audit_kappa=prepared.public_audit[10];
        let crate::r17_relation::Prepared{mut p,iv_g,mut weights,mut claim,..}=prepared;
        assert_eq!(p.gamma,gamma);
        let gp=gamma.pow(27);let mut qeval=[Vec::new(),Vec::new()];
        for(i,pt)in pts.iter().enumerate(){for(slot,(x,y))in[(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate(){
            let all=(0..29).rev().fold(K::ZERO,|acc,col|acc.mul(gamma).add(if col<26{K::from_cm31(CM31::from_m31(encoded[col][4*i+slot]))}else{c2encoded[col-26][4*i+slot]}));
            let g=gp.mul(c2encoded[1][4*i+slot]);let l=p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y));
            for c in 0..2{let iv=if c==0{p.iv}else{iv_g};let value=if c==0{all.sub(g)}else{g};
                qeval[c].push(value.sub(iv[0].add(iv[1].mul_m31(if p.use_x{x}else{y}))).mul(l.try_inv().unwrap()));}
        }}
        let q=[decoder.solve_wide(&qeval[0]),decoder.solve_wide(&qeval[1])];
        for c in 0..2{assert_eq!(q[c][1023],K::ZERO);assert_eq!(p.abc[1].mul(q[c][1022]).sub(p.abc[2].mul(q[c][1021])),K::ZERO);}
        let wr:Vec<_>=(0..1024).map(|i|weights[0].weight_at(i)).collect();
        let wg:Vec<_>=(0..1024).map(|i|weights[1].weight_at(i)).collect();
        let sent=crate::r19_channel_fold::prover_message(&q[0],&q[1],&wr,&wg).unwrap();
        v[417]=sent[0];v[418]=sent[1];
        let (beta,newclaim)=crate::r17_relation::channel_challenge(&mut p,claim,sent).unwrap();claim=newclaim;
        let original_q=q.clone();
        let combined_q:Vec<_>=q[0].iter().zip(&q[1]).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect();
        let combined_w:Vec<_>=wr.iter().zip(&wg).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect();
        assert_eq!(dot(&combined_q,&combined_w),claim,"channel boundary then beta");
        let q=[combined_q,vec![K::ZERO;1024]];
        weights=[WeightAccumulator::empty(10),WeightAccumulator::empty(10)];
        weights[0].add_dense(combined_w).unwrap();
        let first=crate::r17_relation::polynomial(&q,&weights);
        assert_eq!(corelib::sumcheck::boundary_sum(&first),claim);
        f::save_round(&mut v,0,first);absorb_round(&mut p.t,0,&first);
        p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&[0;9]);
        let alpha=sample(&mut p.t,false).unwrap();claim=evaluate(&first,alpha);
        for c in 0..2{weights[c].fold_deferred_relation_arity4(alpha);}
        let mut finals=[primal(&q[0],alpha),primal(&q[1],alpha)];
        v[443..699].copy_from_slice(&finals[0]);
        let nonces=[0u8;24];let stress_attempts=0u64;
        let(queries,rho)=query_schedule(&mut p,&v[443..699],&nonces).unwrap();
        if let Some((other,other_compiled))=&alternate{
            let base:Vec<Vec<M31>>=(0..16).map(|c|(0..1024).map(|r|other_compiled.semantic_c1.c1[c][r].sub(compiled.semantic_c1.c1[c][r])).collect()).collect();
            assert_eq!(base[3][1014],M31::ZERO);
            let delta=r17_c1_witness_audit(&base,&s.z,p.points,&queries,&enc);
            let mut corrected=trace.clone();for c in 0..16{for r in 0..1024{corrected.c1[c][r]=corrected.c1[c][r].add(delta[c][r]);}}
            let public=match payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p,_=>panic!("fixture transfer only")};
            assert_eq!(we::extract_checked(&corrected,&public,&transition,authoritative).unwrap(),*other);
            let before=aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(&compiled.trace,snapshot.next_pair_index,lambda,chi).unwrap();
            let after=aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(&other_compiled.trace,snapshot.next_pair_index,lambda,chi).unwrap();
            let changed=before.iter().zip(&after).filter(|(a,b)|a!=b).count();
            let h1_ood_delta=r17_h1_witness_ood_audit(&before,&after,p.points);
            let (h1_joint_delta,rest_q_delta)=r17_h1_witness_joint_audit(&h1_ood_delta,&delta,&s.z,&p,alpha,&queries,&enc,&decoder);
            if std::env::var_os("ASPIS_R84_H1_PREFLIGHT").is_some() && std::env::var_os("ASPIS_R84_THROUGH_G").is_none() {
                println!("R84_H1_PREFLIGHT_PASS actual_source_prefix=true complete_proof=false privacy_proved=false");
                std::process::exit(0);
            }
            let total_pad:Vec<_>=(0..1024).map(|r|h1_joint_delta[r].sub(after[r].sub(before[r]))).collect();
            let mut applied_pad=vec![K::ZERO;1024];apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied_pad,&total_pad).unwrap();assert_eq!(applied_pad,total_pad);
            let mut alternate_messages=messages.clone();
            for c in 0..16{for r in 0..1024{alternate_messages[c][r]=alternate_messages[c][r].add(K::from_cm31(CM31::from_m31(delta[c][r])));}}
            for r in 0..1024{alternate_messages[26][r]=alternate_messages[26][r].add(h1_joint_delta[r]);}
            let semantic_delta=r17_witness_semantic_delta(&payment,&transition,&messages,&alternate_messages,&s);
            let alternate_initial=crate::r17_relation::initial(state_only_initial_mask_claim(&corrected,&masks.mask_only_c1,&masks.g).unwrap(),&masks.g);
            assert_eq!(semantic_delta[0],alternate_initial.sub(initial),"source initial affine target");
            let g_delta=r17_g_witness_audit(&semantic_delta,&rest_q_delta,&s.z,&p,audit_kappa,alpha,beta,&queries,&enc);
            for r in 0..1024{alternate_messages[27][r]=alternate_messages[27][r].add(g_delta[r]);}
            // Independently reconstruct the G quotient difference from actual
            // encoded values and the existing decoder, not the matrix basis.
            let gc=enc.encode_c2_message(&crate::r16_basis_transport::transport().forward(&g_delta)).unwrap();
            let mut gv=Vec::new();
            for (i,pt) in pts.iter().enumerate(){for (slot,(x,y)) in [(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate(){
                gv.push(gc[4*i+slot].mul(p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y)).try_inv().unwrap()));
            }}
            let gq=decoder.solve_wide(&gv);
            let qr:Vec<_>=original_q[0].iter().zip(&rest_q_delta).map(|(&a,&d)|a.add(d)).collect();
            let qg:Vec<_>=original_q[1].iter().zip(&gq).map(|(&a,&d)|a.add(gp.mul(d))).collect();
            assert_eq!(crate::r19_channel_fold::prover_message(&qr,&qg,&wr,&wg).unwrap(),sent,"both actual channel coefficients retained");
            let mut wb=WeightAccumulator::empty(10);wb.add_dense(wr.iter().zip(&wg).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect()).unwrap();
            let qb:Vec<_>=qr.iter().zip(&qg).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect();
            assert_eq!(polynomial_for_extension(&qb,&wb),first,"new first relation polynomial retained");
            assert_eq!(primal(&qb,alpha),finals[0],"new Final256 retained");
            println!("R19_CHANNEL_WITNESS source_p0_p2_retained=true first_relation_all7=true combined_final256=true decoder_independent=true fixed_prefix_only=true");
            assert_eq!(crate::r17_relation::initial(state_only_initial_mask_claim(&corrected,&masks.mask_only_c1,&alternate_messages[27]).unwrap(),&alternate_messages[27]),initial,"corrected source initial claim");
            assert!(r17_witness_semantic_delta(&payment,&transition,&messages,&alternate_messages,&s).iter().all(|&v|v==K::ZERO));
            println!("R17_C1_WITNESS_VALIDATED same_public=true opposite_selected_input=true actual_helper_rebuilt=true helper_changed_rows={changed} fixed_prefix_diagnostic_only=true");
            if std::env::var_os("ASPIS_R84_THROUGH_G").is_some() {
                println!("R84_FULL_AFFINE_PREFLIGHT_PASS actual_source_prefix=true complete_proof=false privacy_proved=false");
                std::process::exit(0);
            }

        }
        if std::env::var_os("ASPIS_R17_COUPLED_AUDIT").is_some(){r17_coupled_audit::run(h1_coordinates.as_ref().unwrap(),&s.z,&p,audit_kappa,alpha,&queries,|delta|{
            let codeword=enc.encode_c2_message(&crate::r16_basis_transport::transport().forward(delta)).unwrap();
            for &id in &queries{for slot in 0..4{assert_eq!(codeword[4*id as usize+slot],K::ZERO);}}
        });}
        let records:Vec<u8>=queries.iter().flat_map(|&id|{let i=id as usize;let mut r=c1leaf(&encoded,i);r.extend(c2leaf(&c2encoded,i,false));r.extend(salts[i]);r}).collect();
        let fa=crate::r102_tree::frontier(&a,&queries);let fb=crate::r102_tree::frontier(&b,&queries);
        let mut stub=f::body(&v,&a,&b,&records,(&fa,&fb));
        stub[FIXED*16+52..HEAD].copy_from_slice(&nonces);let w=parse(&stub).unwrap();
        let(values,xs)=crate::r17_relation::opened(&w,&p,iv_g,&queries,alpha).unwrap();
        let values=[values[0].iter().zip(&values[1]).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect::<Vec<_>>(),vec![K::ZERO;Q]];
        for c in 0..2{for i in 0..Q{assert_eq!(values[c][i],corelib::v6_onefold::evaluate_final256_coefficients(&finals[c],xs[i]).unwrap());}}
        let inc=crate::r17_relation::inject_two(&mut weights,&mut claim,&values,&xs,rho).unwrap();p.t.absorb(label::PROFILE,&bytes(&[inc]));
        for r in 1..4{let poly=crate::r17_relation::polynomial(&finals,&weights);assert_eq!(corelib::sumcheck::boundary_sum(&poly),claim);
            f::save_round(&mut v,r,poly);absorb_round(&mut p.t,r,&poly);let a=sample(&mut p.t,false).unwrap();claim=evaluate(&poly,a);
            for c in 0..2{weights[c].fold_deferred_relation_arity4(a);finals[c]=primal(&finals[c],a);}}
        let mut body=f::body(&v,&a,&b,&records,(&fa,&fb));
        body[FIXED*16+52..HEAD].copy_from_slice(&nonces);
        #[cfg(v8_semantic_rejoin)] std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();
        phase(seed,"relation_openings_serialize",clock);
        phase(seed,"prover_total_excludes_setup",total);
        // Verifier starts from bytes and public inputs; no witness/anchor.
        let clock=Instant::now();
        let verify=|body:&[u8]|super::super::performance_verifier::verify_payment(body,&binding,&payment,&transition);
        #[cfg(v8_early_prefix)] super::super::early_c1_trace::begin();
        #[cfg(v8_semantic_rejoin)] super::super::semantic_rejoin_oracle_phase(1);
        let selected_verify_result=verify(&body);
        #[cfg(v8_semantic_rejoin)] println!("SEMANTIC_REJOIN_SELECTED_VERIFIER result={selected_verify_result:?} body_bytes={}",body.len());
        #[cfg(not(v8_semantic_rejoin))] assert_eq!(selected_verify_result,Ok(()));
        #[cfg(v8_early_prefix)] super::super::early_c1_trace::check_execution(early_c1,super::super::early_c1_trace::freeze(),a[18][0],&queries,&records);
        if matches!(payment,PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)){
            #[cfg(v8_semantic_rejoin)] super::super::semantic_rejoin_oracle_phase(2);
            let raw_verify_result=super::super::performance_verifier::verify(&body,&binding,&public_bytes,&transition_bytes);
            #[cfg(v8_semantic_rejoin)] println!("SEMANTIC_REJOIN_SELECTED_RAW_VERIFIER result={raw_verify_result:?}");
            assert_eq!(selected_verify_result,raw_verify_result);
        }
        #[cfg(v8_semantic_rejoin)] super::super::semantic_rejoin_oracle_phase(3);
        phase(seed,"host_verify_from_public_bytes",clock);
        for index in [0,HEAD,body.len()-1,417*16,418*16,443*16] {
            let mut bad=body.clone();bad[index]^=1;
            assert!(verify(&bad).is_err());
        }
        assert!(verify(&body[..body.len()-1]).is_err());
        let mut noncanonical=body.clone();noncanonical[443*16..443*16+4].copy_from_slice(&corelib::field::P.to_le_bytes());
        assert!(verify(&noncanonical).is_err());
        #[cfg(v8_semantic_rejoin)] super::super::semantic_rejoin_oracle_report();
        #[cfg(not(v8_semantic_rejoin))] std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();
        #[cfg(not(v8_semantic_rejoin))] println!("R19_CONTROL semantic_rounds=10 channel_fields=2 final_values=256 privacy_gate_open=true corrupted_bytes=6 noncanonical_g_final=true truncated=true deferred_dense_agree=true");
        #[cfg(not(v8_semantic_rejoin))] println!("PERF {{\"seed\":{seed},\"accepted\":true,\"body_bytes\":{},\"max_body_bytes\":59138,\"stress_nonce_attempts\":{stress_attempts},\"security_credit_bits\":0,\"full_transaction_cu\":null}}",body.len());
        #[cfg(v8_semantic_rejoin)] println!("SEMANTIC_REJOIN_COMPLETE controls=passed body_bytes={} diagnostic_only=true",body.len());
    }
}
