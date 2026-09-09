//! SAME-execution payment/masking/semantic/relation + authenticated C1 recovery.
//! Synthetic accounts, explicit extra-opening oracle; no real replay extractor.
use super::*;
use super::{authenticated_c1 as ac,fixtures as f,inactive_binding as row,witness_endpoint as we};
use super::state_only_hiding::*;
use aspis_statement::{pool_v1::*,multilinear_evaluate_qm31};
use corelib::state_only_sumcheck::{begin_state_only_zerocheck,state_only_boundary_sum,evaluate_state_only_polynomial};
use corelib::state_only_hiding::{StateOnlyHidingContext,begin_state_only_masked_sumcheck};
use circle_candidate::CircleEncoder;
const N:usize=1<<20;
#[cfg(v8_performance)]
#[path="performance.rs"]
pub(super) mod performance;
fn tree(leaves:Vec<[u8;26]>)->f::Tree{let mut t=vec![leaves];for _ in 0..18{t.push(t.last().unwrap().chunks_exact(2).map(|v|node_hash_v7(hash,&v[0],&v[1])).collect());}t}
fn c1leaf(columns:&[Vec<M31>],id:usize)->Vec<u8>{let mut b=vec![0;403];
    for s in 0..4{for col in 0..26{ac::put31(&mut b,31*(s*26+col),columns[col][4*id+s]);}}
    // Predetermined BEFORE commitment: encode p (the sole invalid 31-bit
    // limb), never reduce it modulo p or change the committed raw bytes.
    #[cfg(v8_c1_noncanonical)]
    if id==0||id==256{for slot in 0..4{for j in 0..31{let bit=31*(slot*26)+j;b[bit/8]|=1<<(bit%8);}}}
    b}
fn c2leaf(columns:&[Vec<K>],id:usize,corrupt:bool)->Vec<u8>{let mut b=vec![0;186];
    for s in 0..4{for col in 0..3{let mut v=columns[col][4*id+s];if corrupt&&id<9302&&col==2{v=v.add(K::ONE);}
        let bytes=bytes(&[v]);for limb in 0..4{let x=M31(u32::from_le_bytes(bytes[4*limb..4*limb+4].try_into().unwrap()));
            ac::put31(&mut b,31*(col*16+s*4+limb),x);}}}b}
fn point_rows(messages:&[Vec<K>],z:&[K;10])->Vec<K>{
    corelib::v6_transcript::v6_statement_points(z).iter().flat_map(|p|messages.iter().map(move|m|multilinear_evaluate_qm31(m,p).unwrap())).collect()
}
trait PaymentInput {fn payment(&self)->PoolV1PairForestTerminalPaymentV1;}
impl PaymentInput for PoolV1PrivateTransferPublicV1 {fn payment(&self)->PoolV1PairForestTerminalPaymentV1{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(*self)}}
impl PaymentInput for PoolV1PairForestTerminalPaymentV1 {fn payment(&self)->PoolV1PairForestTerminalPaymentV1{*self}}
fn payment_terminal(p:&impl PaymentInput,tr:&PoolV1PairLatePublicStatementV1,claims:&[K;84],z:&[K;10],s:&row::Semantic)->K{
    let value=match p.payment(){
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(&p,tr,claims,z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta),
        PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1(&p,tr,claims,z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta),
    }.unwrap();
    #[cfg(v8_positive_transfer)] {
        assert!(matches!(p.payment(),PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)),"positive profile is transfer-only");
        return value.add(super::positive_transfer::terminal_delta(claims,z,s.theta,&s.zc,s.eta));
    }
    #[cfg(not(v8_positive_transfer))] value
}
fn terminal(p:&impl PaymentInput,tr:&PoolV1PairLatePublicStatementV1,m:&[Vec<K>],z:&[K;10],s:&row::Semantic)->K{
    let rows=point_rows(m,z);let claims:[K;84]=std::array::from_fn(|i|rows[(i/28)*29+i%28]);
    payment_terminal(p,tr,&claims,z,s)
}
fn start(binding:&[u8;32],a:&f::Tree)->(Transcript,K,K){let mut t=Transcript::new(hash);
    #[cfg(v8_positive_transfer)] super::positive_transfer::absorb(&mut t);
    t.absorb(label::PROFILE,b"AV8/payment-extraction/v1");t.absorb(label::STATEMENT,binding);t.absorb(label::ROOT,&a[18][0]);
    let lambda=sample(&mut t,false).unwrap();let chi=sample(&mut t,false).unwrap();(t,lambda,chi)}
fn semantic_start(mut t:Transcript,b:&f::Tree,initial:K,lambda:K,chi:K)->row::Semantic{
    t.absorb(label::SECOND_PHASE_ROOT,&b[18][0]);let bat=begin_state_only_zerocheck(&mut t).unwrap();
    let eta=begin_state_only_masked_sumcheck(&mut t,initial).unwrap();
    row::Semantic{t,z:[K::ZERO;10],lambda,chi,theta:bat.theta,zc:bat.zerocheck_point,mu:bat.mu,eta,claim:initial}
}
fn interpolate_degree27(values: &[K; 28]) -> [K;28] {
    let mut output = [K::ZERO; 28];
    for i in 0..28 {
        let mut basis = [K::ZERO; 28];
        basis[0] = K::ONE;
        let mut basis_degree = 0usize;
        let mut denominator = M31::ONE;
        for j in 0..28 {
            if i == j {
                continue;
            }
            let root = M31(j as u32);
            let previous = basis;
            for coefficient in 0..=basis_degree + 1 {
                let shifted = if coefficient == 0 {
                    K::ZERO
                } else {
                    previous[coefficient - 1]
                };
                let constant = if coefficient <= basis_degree {
                    previous[coefficient].mul_m31(root)
                } else {
                    K::ZERO
                };
                basis[coefficient] = shifted.sub(constant);
            }
            basis_degree += 1;
            denominator = denominator.mul(M31(i as u32).sub(root));
        }
        let scale = values[i].mul_m31(denominator.inv());
        for coefficient in 0..28 {
            output[coefficient] = output[coefficient].add(scale.mul(basis[coefficient]));
        }
    }
    output
}

fn semantic_produce(v:&mut[K],mut s:row::Semantic,p:&impl PaymentInput,tr:&PoolV1PairLatePublicStatementV1,m:&[Vec<K>])->row::Semantic{
    // Literal selected producer enumeration/interpolation; only framing is
    // the repaired research grammar, and the selected terminal is called.
    for r in 0..10{let left=9-r;let mut samples=[K::ZERO;28];
        for x in 0..28{let mut z=s.z;z[r]=sc(x as u32);
            for assignment in 0..1<<left{for j in 0..left{z[r+1+j]=sc(((assignment>>(left-1-j))&1)as u32);}
                samples[x]=samples[x].add(terminal(p,tr,m,&z,&s));}}
        let poly=interpolate_degree27(&samples);
        assert_eq!(state_only_boundary_sum(&poly),s.claim,"genuine semantic boundary round {r}");
        let sent=&mut v[1+27*r..1+27*(r+1)];sent[0]=poly[0];sent[1..].copy_from_slice(&poly[2..]);
        let mut record=vec![r as u8];record.extend(bytes(sent));s.t.absorb(label::V6_COMPACT_SEMANTIC_ROUND,&record);
        s.z[r]=sample(&mut s.t,false).unwrap();s.claim=evaluate_state_only_polynomial(&poly,s.z[r]);
        println!("semantic_round={r} checked=true");
    }
    assert_eq!(terminal(p,tr,m,&s.z,&s),s.claim);s
}
fn semantic_replay(w:&Wire,p:&impl PaymentInput,tr:&PoolV1PairLatePublicStatementV1,mut s:row::Semantic)->row::Semantic{
    for r in 0..10{let sent=&w.v[1+27*r..1+27*(r+1)];let mut poly=[K::ZERO;28];poly[0]=sent[0];poly[2..].copy_from_slice(&sent[1..]);
        poly[1]=s.claim.sub(poly[0].add(poly[0]).add(poly[2..].iter().copied().fold(K::ZERO,|a,b|a.add(b))));
        let mut record=vec![r as u8];record.extend(bytes(sent));s.t.absorb(label::V6_COMPACT_SEMANTIC_ROUND,&record);
        s.z[r]=sample(&mut s.t,false).unwrap();s.claim=evaluate_state_only_polynomial(&poly,s.z[r]);}
    let claims:[K;84]=std::array::from_fn(|i|w.v[271+(i/28)*29+i%28]);
    let value=payment_terminal(p,tr,&claims,&s.z,&s);assert_eq!(value,s.claim);s
}
#[cfg(v8_positive_transfer)]
fn semantic_negative_fixture(v:&mut[K],mut s:row::Semantic,p:&impl PaymentInput,
    tr:&PoolV1PairLatePublicStatementV1,m:&[Vec<K>])->row::Semantic{
    // Adversarial diagnostic ONLY: send the literal true-sum polynomials for
    // a false zero-check, even though the initial claimed sum is wrong. The
    // actual verifier still reconstructs every omitted coefficient from its
    // own carried claim. No future challenge is forced or consulted.
    let mut first_boundary_wrong=false;
    for r in 0..10{let left=9-r;let mut samples=[K::ZERO;28];
        for x in 0..28{let mut z=s.z;z[r]=sc(x as u32);
            for assignment in 0..1<<left{for j in 0..left{z[r+1+j]=sc(((assignment>>(left-1-j))&1)as u32);}
                samples[x]=samples[x].add(terminal(p,tr,m,&z,&s));}}
        let poly=interpolate_degree27(&samples);
        if r==0{first_boundary_wrong=state_only_boundary_sum(&poly)!=s.claim;}
        let sent=&mut v[1+27*r..1+27*(r+1)];sent[0]=poly[0];sent[1..].copy_from_slice(&poly[2..]);
        let mut record=vec![r as u8];record.extend(bytes(sent));s.t.absorb(label::V6_COMPACT_SEMANTIC_ROUND,&record);
        s.z[r]=sample(&mut s.t,false).unwrap();s.claim=evaluate_state_only_polynomial(&poly,s.z[r]);
    }
    assert!(first_boundary_wrong,"fixed negative fixture encountered legitimate cancellation; record rather than retry");
    assert_eq!(terminal(p,tr,m,&s.z,&s),s.claim);
    println!("POSITIVE_NEGATIVE genuine_terminal_polynomials=true first_boundary_wrong=true future_challenges_forced=false");s
}
fn ood(m:&[K],p:Point)->K{let mut factors=[K::ZERO;10];factors[0]=p.y;factors[1]=p.x;
    for i in 2..10{factors[i]=factors[i-1].square().mul_m31(M31(2)).sub(K::ONE);}
    m.iter().enumerate().fold(K::ZERO,|sum,(j,c)|{let mut v=*c;for bit in 0..10{if j&(1<<bit)!=0{v=v.mul(factors[bit]);}}sum.add(v)})}
fn provision_accounts(w:&PoolV1PairForestPrivateTransferWitnessV1)->PoolV1PaymentRuntimeBindingV1{
    // Synthetic trusted setup provisions the retained account root from the
    // tree, independently of the prover's public-statement fields. This is
    // not a Solana account-authentication implementation.
    let mut root=w.input.pair.pair_leaf.leaf_digest().unwrap();
    for i in 0..20{let sibling=w.input.pair.membership.siblings[i];root=if(w.input.pair.membership.index>>i)&1==0{
        pool_v1_tree_parent(&root,&sibling)}else{pool_v1_tree_parent(&sibling,&root)};}
    for i in 0..3{let sibling=w.input.super_root_siblings[i];root=if w.input.super_root_directions[i]{
        pool_v1_tree_parent(&sibling,&root)}else{pool_v1_tree_parent(&root,&sibling)};}
    PoolV1PaymentRuntimeBindingV1{pool:[1;32],deployment_domain:[2;32],anchor_sequence:42,anchor_root:root,asset_id:M31(77)}
}
pub fn run(){
    let total=std::time::Instant::now();
    #[cfg(v8_query_graph)] super::query_graph::controls();
    #[cfg(v8_c1_gao)] super::c1_gao::controls();
    let mask_set:std::collections::BTreeSet<(usize,usize)>=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap()
        .iter().map(|c|(c.row as usize,c.column as usize)).collect();
    let path=|l:usize|913+16*(l/4)+4*(l%4);
    for l in 0..24{assert_eq!(Some(path(l)),pool_v1_pair_forest_path_base_row_v1(l));}
    for r in 0..1024{for c in 0..16{
        let paths=(0..24).any(|l|(r==path(l)&&c<=8)||r==path(l)+1);
        let values=(0..3).any(|v|(r==1008+2*v||r==1009+2*v||r==((1008+2*v)^12))&&c<=10)
            ||(r==1014&&c<3)||(r==1015&&c<2);
        let occupancy=(r==1017&&c<=10)||(r==1018&&c<10);
        let mask=(r<912&&r%16>=13)||(r>=912&&!((r<1008&&paths)||(r>=1008&&(values||occupancy))));
        assert_eq!(mask,mask_set.contains(&(r,c)),"source/Lean mask layout at {r},{c}");
        let read=[12,28,44,60,444,460,476,492,508,524].contains(&r)
            ||(0..24).any(|l|(r==path(l)&&c==0)||r==path(l)+1)||(r==1017&&c<2);
        assert!(!(read&&mask));
    }}
    println!("source_lean_layout_cells=16384 mask_cells={} read_mask_intersection=0",mask_set.len());
    // Fixed independent setup/account fixture. Producer and extractor receive
    // copies; mutation of a prover public value cannot mutate this context.
    let(public,witness,snapshot)=we::fixture();let account_binding=provision_accounts(&witness);
    let authoritative=PoolV1PaymentRelationContextV1{runtime_binding:account_binding,spent_nullifiers:&[]};
    assert_eq!(we::context(&public).runtime_binding,account_binding);
    let compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,&witness,authoritative,snapshot).unwrap();
    let transition=compiled.public_statement;
    let enc=CircleEncoder::new_for_domain_log(20);
    println!("stage=public_generator_rank");
    let matrix_start=std::time::Instant::now();let decoder=ac::Decoder::new(&enc);assert_eq!(decoder.pivots,1024);
    println!("public_matrix_seconds={}",matrix_start.elapsed().as_secs_f64());
    #[cfg(v8_query_graph)]
    let second_decoder={let t=std::time::Instant::now();let d=ac::Decoder::new_at(&enc,1024);assert_eq!(d.pivots,1024);
        println!("second_matrix_start=1024 rank={} seconds={}",d.pivots,t.elapsed().as_secs_f64());d};
    let domain_points=corelib::circle_fri::selected_circle_fiber_points_shared(20,&(0..(N/4)as u32).collect::<Vec<_>>()).unwrap();
    println!("rank=1024 stage=producer");
    // Final fixed cohort, every arm retained. Seed1 was the packing preflight;
    // seeds2..4 are declared before this cohort executes. No stop on success.
    #[cfg(not(v8_c1_boundary))] let seeds=vec![1u8,2,3,4];
    #[cfg(v8_c1_boundary)] let seeds=vec![1u8]; // predeclared, no search
    for seed in seeds{
    println!("seed={seed}");
    #[cfg(v8_query_graph)] super::query_graph::begin();
    let binding=hash(&[b"AV8 synthetic account fixture", &encode_pool_v1_private_transfer_public_v1(&public).unwrap(),
        format!("{transition:?}").as_bytes()]);
    let hc=StateOnlyHidingContext::pool_v1_pair_forest_v1(binding,[seed;32]);
    let attempt=state_only_entropy::StateOnlyAttemptSecrets::deterministic_spend_fixture([seed;32],[seed+1;32],[seed+2;32]);
    let(reserved,material)=attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,binding,hc,&mut InMemoryStateOnlyMaskNonceStore::default()).unwrap();
    let d=reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,hc).unwrap();
    let mut trace=compiled.semantic_c1.clone();let masks=apply_pool_v1_pair_forest_mask_material_v1(&mut trace,material).unwrap();
    let selected:Vec<Vec<M31>>=trace.c1.iter().chain(masks.mask_only_c1.iter()).cloned().collect();
    let mut encoded:Vec<Vec<M31>>=selected.iter().map(|m|enc.encode_c1_message(m).unwrap()).collect();
    let anchor_prefix:Vec<Vec<M31>>=encoded.iter().map(|c|c[..1024].to_vec()).collect();
    #[cfg(all(v8_c1_boundary,not(v8_c1_first_window)))] let corrupt_c1_fibre=256;
    #[cfg(all(v8_c1_boundary,v8_c1_first_window))] let corrupt_c1_fibre=0;
    #[cfg(all(v8_c1_boundary,not(v8_c1_near),not(v8_c1_noncanonical)))]
    for slot in 0..4{encoded[0][4*corrupt_c1_fibre+slot]=encoded[0][4*corrupt_c1_fibre+slot].add(M31::ONE);}
    #[cfg(all(v8_c1_both_windows,not(v8_c1_near),not(v8_c1_noncanonical)))]
    for slot in 0..4{encoded[0][4*256+slot]=encoded[0][4*256+slot].add(M31::ONE);}
    #[cfg(v8_c1_near)]
    for fibre in 0..16535{for slot in 0..4{encoded[0][4*fibre+slot]=encoded[0][4*fibre+slot].add(M31::ONE);}}
    let salts:Vec<[u8;32]>=(0..N/4).map(|i|reserved.derive_pool_v1_leaf_salt(hash,hc,0x77,i as u32).unwrap()).collect();
    let a=tree((0..N/4).map(|i|private_leaf_hash_v7(hash,V7_C1_TREE_TAG,&c1leaf(&encoded,i),&salts[i])).collect());
    // The graph variant supplies this bundle ONLY from the frozen SHA query
    // log, without receiving the producer's encoded columns/tree/salts.
    #[cfg(not(v8_query_graph))]
    let openings=ac::C1Openings{ids:(0..256).collect(),leaves:(0..256).map(|i|c1leaf(&encoded,i)).collect(),
        salts:salts[..256].to_vec(),frontier:f::frontier(&a,&(0..256).collect::<Vec<_>>())};
    #[cfg(v8_query_graph)]
    let (openings,extracted)={let log=super::query_graph::freeze();let begin=std::time::Instant::now();
        #[cfg(not(v8_c1_noncanonical))]
        let ex=super::query_graph::extract(&log,a[18][0],18,(1<<19)-1).unwrap();
        #[cfg(v8_c1_noncanonical)]
        let ex={assert!(matches!(super::query_graph::extract(&log,a[18][0],18,(1<<19)-1),Err(super::query_graph::Failure::Canonical)));
            let ex=super::query_graph::extract_raw(&log,a[18][0],18,(1<<19)-1).unwrap();
            for fibre in [0,256]{for slot in 0..4{assert!(ac::read31(&ex.leaves[fibre].value,31*(slot*26)).is_err());assert_eq!(ex.totalized_value(fibre,slot,0).unwrap(),M31::ZERO);}}
            println!("RAW_C1 strict_rejects=true raw_root_verified=true invalid_limbs=8 totalized_zero=true");ex};
        let exact=ex.recover_exact(&decoder,&enc);
        #[cfg(not(v8_c1_boundary))] assert!(exact.is_ok());
        #[cfg(all(v8_c1_boundary,not(v8_c1_noncanonical)))] assert!(matches!(&exact,Err(super::query_graph::Failure::NotCodeword)));
        #[cfg(v8_c1_noncanonical)] assert!(matches!(&exact,Err(super::query_graph::Failure::Canonical)));
        // The checked-witness extractor must not require exact received-word
        // membership: a corrupt word can still disclose a valid witness.
        let mut recovered=None;
        for (window,d) in [&decoder,&second_decoder].into_iter().enumerate(){
            let candidate=match ex.candidate_at(d){Ok(c)=>c,Err(e)=>{println!("CANDIDATE window={window} decode_error={e:?} checked_witness=false");continue}};
            let valid=we::extract_checked(&candidate,&public,&transition,authoritative).is_ok();
            println!("CANDIDATE window={window} checked_witness={valid}");
            if valid{recovered=Some(candidate);break;}
        }
        #[cfg(v8_c1_gao)]
        if recovered.is_none() || cfg!(v8_c1_near){
            #[cfg(not(v8_c1_near))] let candidate=super::c1_gao::recover(&ex,&enc,&decoder);
            #[cfg(v8_c1_near)] let candidate=super::c1_gao::recover_near(&ex,&enc,&decoder);
            println!("GAO_CANDIDATE returned={}",candidate.is_ok());
            if let Ok(candidate)=candidate{if we::extract_checked(&candidate,&public,&transition,authoritative).is_ok(){recovered=Some(candidate)}}
        }
        // Failure stays visible while the independent prover continues.
        // Never substitute the producer's trace for a missing candidate.
        #[cfg(not(v8_c1_both_windows))] assert!(recovered.is_some());
        if let Some(candidate)=&recovered{let got=we::extract_checked(candidate,&public,&transition,authoritative).unwrap();assert!(got==witness,"synthetic witness comparison failed");}
        println!("GRAPH_PREFIX seed={seed} checked_witness={} full_semantic_C1_codeword={} pre_lambda_chi=true stats={:?} seconds={}",recovered.is_some(),exact.is_ok(),ex.stats,begin.elapsed().as_secs_f64());
        #[cfg(not(v8_c1_boundary))]
        if seed==1{super::query_graph::outside_sample_control(&log,&ex,&decoder,&enc);}
        (ex.openings(),recovered)
    };
    #[cfg(not(v8_query_graph))]
    let extracted=Some(ac::recover_c1(a[18][0],&openings,&decoder).unwrap());
    if let Some(candidate)=&extracted{
        let got=we::extract_checked(candidate,&public,&transition,authoritative).unwrap();
        assert!(got==witness,"synthetic witness comparison failed");
        println!("recovered_table_equals_producer={}",*candidate==trace);
        #[cfg(not(v8_c1_boundary))] assert!(*candidate==trace,"honest table comparison failed");
    }
    let mut broken=openings.clone();broken.ids[1]=0;assert!(ac::authenticate(a[18][0],&broken).is_err());
    let mut broken=openings.clone();broken.leaves[0][0]^=1;assert!(ac::authenticate(a[18][0],&broken).is_err());
    let mut wrong_root=a[18][0];wrong_root[0]^=1;assert!(ac::authenticate(wrong_root,&openings).is_err());
    let mut broken=openings.clone();broken.frontier.pop();assert!(ac::authenticate(a[18][0],&broken).is_err());
    let mut broken=openings.clone();broken.leaves[0][..3].fill(255);broken.leaves[0][3]|=127;assert!(matches!(ac::authenticate(a[18][0],&broken),Err(Error::Canonical)));
    // Authenticated corruption under a NEW root is not repaired by ordinary
    // interpolation. This is a decoder capability control, not acceptance.
    #[cfg(not(v8_c1_noncanonical))] {
    let mut changed=openings.clone();changed.leaves[0][0]^=1;
    let mut changed_hash=private_leaf_hash_v7(hash,V7_C1_TREE_TAG,&changed.leaves[0],&changed.salts[0]);
    for row in 0..18{changed_hash=node_hash_v7(hash,&changed_hash,&a[row][1]);}
    let bad_coeff=ac::recover_c1(changed_hash,&changed,&decoder).unwrap();
    assert!(we::extract_checked(&bad_coeff,&public,&transition,authoritative).is_err());
    println!("authentication_negative_controls=5 authenticated_changed_C1_decoder_rejected=true");
    }
    #[cfg(v8_c1_noncanonical)] println!("authentication_negative_controls=5 original_sample_noncanonical=true changed_root_interpolation_control=not_applicable");
    println!("authenticated_c1_recovered={} checked_witness={} root={:02x?} opening_bytes={}",extracted.is_some(),extracted.is_some(),a[18][0],256*(403+32)+openings.frontier.len());
    let(t,lambda,chi)=start(&binding,&a);
    let mut h=aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(
        &compiled.trace,snapshot.next_pair_index,lambda,chi).unwrap();
    apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h,&masks.h1_padding).unwrap();
    assert_eq!(aspis_statement::state_only_copy_helper_sum(&h),Some(K::ZERO));
    let c2=vec![h,masks.g.clone(),d];
    let c2encoded:Vec<Vec<K>>=c2.iter().map(|m|enc.encode_c2_message(m).unwrap()).collect();
    let messages:Vec<Vec<K>>=selected.iter().map(|c|c.iter().map(|v|K::from_cm31(CM31::from_m31(*v))).collect()).chain(c2.iter().cloned()).collect();
    let initial=state_only_initial_mask_claim(&trace,&masks.mask_only_c1,&masks.g).unwrap();
    for assignment in 0..1024{let z=std::array::from_fn(|j|sc(((assignment>>(9-j))&1)as u32));let rows=point_rows(&messages,&z);
        let claims=std::array::from_fn(|i|rows[(i/28)*29+i%28]);
        assert_eq!(evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1(
            &public,&transition,&claims,&z,lambda,chi,sc(17)).unwrap(),K::ZERO);}
    println!("masked_selected_boolean_composition_checks=1024");
    #[cfg(not(v8_c1_boundary))] let arms=vec![false,true];
    #[cfg(v8_c1_boundary)] let arms=vec![false];
    for corrupt in arms{
        println!("arm_corrupt={corrupt} stage=commit_C2");
        let b=tree((0..N/4).map(|i|private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&c2leaf(&c2encoded,i,corrupt),&salts[i])).collect());
        let mut v=vec![K::ZERO;697];v[0]=initial;
        let mut s=semantic_produce(&mut v,semantic_start(t.clone(),&b,initial,lambda,chi),&public,&transition,&messages);
        v[271..358].copy_from_slice(&point_rows(&messages,&s.z));
        let empty=vec![0;Q*REC];let stub=f::body(&v,&a,&b,&empty,(&[],&[]));let w=parse(&stub).unwrap();
        row::points_absorb(&mut s.t,&w);
        let p0=s.t.challenge_secure_circle_point().unwrap();for j in 0..29{v[359+j]=ood(&messages[j],p0);}
        let mut rec=vec![0];rec.extend(bytes(&v[359..388]));s.t.absorb(V8_COMPONENT_OOD_VECTOR,&rec);
        let p1=(0..3).map(|_|s.t.challenge_secure_circle_point().unwrap()).find(|p|*p!=p0).unwrap();
        for j in 0..29{v[388+j]=ood(&messages[j],p1);}let mut rec=vec![1];rec.extend(bytes(&v[388..417]));s.t.absorb(V8_COMPONENT_OOD_VECTOR,&rec);
        s.t.absorb(label::M31_PAYMENT_BATCH_POW_NONCE,&[0;8]);let gamma=sample(&mut s.t,true).unwrap();
        let mut iw=WeightAccumulator::empty(10);iw.add_grouped_64x16_binary_masks_deferred_prepared(
            pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1(),pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1()).unwrap();
        let combined:Vec<K>=(0..1024).map(|i|messages.iter().rev().fold(K::ZERO,|x,m|x.mul(gamma).add(m[i]))).collect();
        v[358]=(0..1024).fold(K::ZERO,|sum,i|sum.add(iw.weight_at(i).mul(combined[i as usize])));
        let stub=f::body(&v,&a,&b,&empty,(&[],&[]));let w=parse(&stub).unwrap();
        let sem=semantic_replay(&w,&public,&transition,semantic_start(t.clone(),&b,initial,lambda,chi));
        let(mut p,ordinary,mut claim,_)=row::prepare(sem,&w,true).unwrap();assert_eq!(p.gamma,gamma);
        let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&(0..256).collect::<Vec<_>>()).unwrap();
        let mut qeval=Vec::new();
        for (i,pt) in pts.iter().enumerate(){for(slot,(x,y))in[(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate(){
            let value=(0..29).rev().fold(K::ZERO,|acc,col|acc.mul(gamma).add(if col<26{K::from_cm31(CM31::from_m31(anchor_prefix[col][4*i+slot]))}else{c2encoded[col-26][4*i+slot]}));
            let l=p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y));
            let h=if p.use_x{x}else{y};qeval.push(value.sub(p.iv[0].add(p.iv[1].mul_m31(h))).mul(l.try_inv().unwrap()));}}
        let q=decoder.solve_wide(&qeval);
        assert_eq!(q[1023],K::ZERO,"image E1");assert_eq!(p.abc[1].mul(q[1022]).sub(p.abc[2].mul(q[1021])),K::ZERO,"image E2");
        assert_eq!(claim,dot(&ordinary,&q),"ordinary chord transport");
        // Independent full-domain reconstruction in the actual source FFT
        // convention. This is prover-side diagnostic work, not verifier CU.
        let q_encoded=enc.encode_c2_message(&q).unwrap();let combined_encoded=enc.encode_c2_message(&combined).unwrap();
        for(i,pt)in domain_points.iter().enumerate(){for(slot,(x,y))in[(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate(){
            let l=p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y));assert_ne!(l,K::ZERO);
            let ih=p.iv[0].add(p.iv[1].mul_m31(if p.use_x{x}else{y}));
            assert_eq!(combined_encoded[4*i+slot].sub(ih),l.mul(q_encoded[4*i+slot]));}}
        drop(q_encoded);drop(combined_encoded);
        println!("full_domain_chord_reconstruction_points={N} nonzero_denominators={N}");
        let mut weights=WeightAccumulator::empty(10);weights.add_dense(ordinary).unwrap();
        let mut image=vec![K::ZERO;1024];image[1023]=p.tau;image[1022]=p.tau.square().mul(p.abc[1]);image[1021]=p.tau.square().mul(p.abc[2]).neg();weights.add_dense(image).unwrap();
        f::save_round(&mut v,0,polynomial_for_extension(&q,&weights));
        let first=compact(&v[417..423],claim);absorb_round(&mut p.t,0,&first);p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&[0;9]);
        let alpha=sample(&mut p.t,false).unwrap();claim=evaluate(&first,alpha);weights.fold_deferred_relation_arity4(alpha);
        let mut finals=primal(&q,alpha);v[441..697].copy_from_slice(&finals);let(queries,rho)=query_schedule(&mut p,&finals,&[0;24]).unwrap();
        let records:Vec<u8>=queries.iter().flat_map(|&id|{let i=id as usize;let mut r=c1leaf(&encoded,i);r.extend(c2leaf(&c2encoded,i,corrupt));r.extend(salts[i]);r}).collect();
        let fa=f::frontier(&a,&queries);let fb=f::frontier(&b,&queries);let stub=f::body(&v,&a,&b,&records,(&fa,&fb));let w=parse(&stub).unwrap();
        let(values,xs)=match opened_values(&w,&p,&queries,alpha,hash){Ok(v)=>v,Err(e)=>{
            #[cfg(v8_c1_noncanonical)] {println!("NONCANONICAL_OPENING rejected_at_query_parse={e:?} accepted=false checked_witness={} queried_invalid_fibre={}",extracted.is_some(),queries.contains(&0)||queries.contains(&256));continue;}
            #[cfg(not(v8_c1_noncanonical))] panic!("unexpected synthetic opening error: {e:?}");
        }};
        let mismatches=(0..Q).filter(|&i|corelib::v6_onefold::evaluate_final256_coefficients(&finals,xs[i]).unwrap()!=values[i]).count();
        println!("arm_corrupt={corrupt} pointwise_mismatches={mismatches} prior_exact={}",claim==dot(&finals,&(0..256).map(|i|weights.weight_at(i)).collect::<Vec<_>>()));
        let inc=inject(&mut weights,&mut claim,&values,&xs,rho).unwrap();p.t.absorb(label::PROFILE,&bytes(&[inc]));
        for r in 1..4{f::save_round(&mut v,r,polynomial_for_extension(&finals,&weights));let poly=compact(&v[417+6*r..423+6*r],claim);
            absorb_round(&mut p.t,r,&poly);let alpha=sample(&mut p.t,false).unwrap();claim=evaluate(&poly,alpha);weights.fold_deferred_relation_arity4(alpha);finals=primal(&finals,alpha);}
        let body=f::body(&v,&a,&b,&records,(&fa,&fb));let w=parse(&body).unwrap();
        let sem=semantic_replay(&w,&public,&transition,semantic_start(t.clone(),&b,initial,lambda,chi));
        let(p,weights,claim,_)=row::prepare(sem,&w,true).unwrap();let result=row::relation(&w,p,weights,claim);println!("relation_result={result:?}");let accepted=result.is_ok();
        #[cfg(not(v8_c1_boundary))]
        if !corrupt{assert!(accepted,"honest baseline");}
        assert_eq!(w.roots.0,a[18][0]);
        let checked_witness=extracted.as_ref().is_some_and(|candidate|we::extract_checked(candidate,&public,&transition,authoritative).is_ok());
        println!("RESULT corrupt={corrupt} accepted={accepted} checked_witness={checked_witness} touched={} body={} proof_id={:02x?} c1_root={:02x?}",queries.iter().filter(|&&i|i<9302).count(),body.len(),hash(&[&body]),w.roots.0);
        #[cfg(all(v8_c1_boundary,not(v8_c1_both_windows)))]
        println!("C1_BOUNDARY seed=1 corrupted_complete_fibres=1 fibre={corrupt_c1_fibre} c1_hit={} accepted={accepted} checked_witness={checked_witness} exact_codeword=false",queries.contains(&(corrupt_c1_fibre as u32)));
        #[cfg(all(v8_c1_both_windows,not(v8_c1_near)))]
        println!("C1_BOTH_WINDOWS seed=1 corrupted_complete_fibres=2 c1_hit={} accepted={accepted} checked_witness={checked_witness} candidate_exhaustion={}",queries.contains(&0)||queries.contains(&256),extracted.is_none());
        #[cfg(v8_c1_noncanonical)] println!("NONCANONICAL_C1 same_execution=true accepted={accepted} checked_witness={checked_witness} queried_invalid_fibre={}",queries.contains(&0)||queries.contains(&256));
        #[cfg(v8_c1_near)]
        println!("C1_NEAR_CONTROL seed=1 corrupted_complete_fibres=16535 c1_hits={} accepted={accepted} checked_witness={checked_witness}",queries.iter().filter(|&&i|i<16535).count());
    }
    }
    #[cfg(not(v8_query_graph))]
    println!("COMPLETE same_execution_access=extra_authenticated_opening_oracle seconds={}",total.elapsed().as_secs_f64());
    #[cfg(v8_query_graph)]
    println!("COMPLETE same_execution_access=frozen_C1_SHA_query_graph seconds={}",total.elapsed().as_secs_f64());
}
