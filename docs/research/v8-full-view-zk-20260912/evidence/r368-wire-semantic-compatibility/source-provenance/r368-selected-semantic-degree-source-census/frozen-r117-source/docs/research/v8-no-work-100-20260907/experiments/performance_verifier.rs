//! Shared host/SBF research verifier, public byte input only.
//! Does NOT authenticate caller/account context or settle a pool transaction.
use super::*;
use super::inactive_binding as row;
use aspis_statement::pool_v1::*;
use corelib::state_only_sumcheck::{begin_state_only_zerocheck,evaluate_state_only_polynomial};
use corelib::state_only_hiding::begin_state_only_masked_sumcheck;
#[cfg(all(v8_block_horner,not(v8_semantic_carry)))]
#[inline(never)]
fn semantic_eval(poly:&[K;28],alpha:K)->K {
    use corelib::field::{PreparedQm31Multiplier as P,qm31_sum_products3_prepared};
    let a2=alpha.square();let a3=a2.mul(alpha);let a4=P::new(a2.square());
    let powers=[P::new(alpha),P::new(a2),P::new(a3)];
    let mut blocks=poly.chunks_exact(4).rev();
    let first=blocks.next().unwrap();
    let mut out=first[0].add(qm31_sum_products3_prepared(&powers,&[first[1],first[2],first[3]]));
    for c in blocks{out=a4.mul(out).add(c[0]).add(qm31_sum_products3_prepared(&powers,&[c[1],c[2],c[3]]));}
    #[cfg(not(v8_performance_sbf))]
    assert_eq!(out,evaluate_state_only_polynomial(poly,alpha));
    out
}
#[cfg(v8_semantic_carry)]
#[inline(never)]
fn semantic_eval(poly:&[K;28],alpha:K)->K {super::semantic_carry::evaluate(poly,alpha)}
pub(super) fn checkpoint(name:&str){
    #[cfg(all(v8_performance_sbf,not(v8_quiet_profile)))] {
        ();
        ();
    }
    #[cfg(any(not(v8_performance_sbf),v8_quiet_profile))] let _=name;
}
#[inline(never)]
fn semantic(w:&Wire<'_>,binding:&[u8;32],public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1)->Result<row::Semantic,Error>{
    semantic_cached(w,binding,public,transition,&mut [])
}
#[inline(never)]
fn semantic_cached(w:&Wire<'_>,binding:&[u8;32],public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1,cache:&mut[K])->Result<row::Semantic,Error>{
    assert!(cache.is_empty() || cache.len()==271);
    let mut t=Transcript::new(hash);t.absorb(label::PROFILE,b"AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1");
    #[cfg(v8_positive_transfer)] super::positive_transfer::absorb(&mut t);
    t.absorb(label::PROFILE,b"AV8/payment-extraction/v1");
    t.absorb(label::STATEMENT,binding);t.absorb(label::ROOT,&w.roots.0);
    let lambda=sample(&mut t,false)?;let chi=sample(&mut t,false)?;
    t.absorb(label::SECOND_PHASE_ROOT,&w.roots.1);
    let bat=begin_state_only_zerocheck(&mut t).map_err(|_|Error::Sampler)?;
    let eta=begin_state_only_masked_sumcheck(&mut t,w.v[0]).map_err(|_|Error::Sampler)?;
    let mut s=row::Semantic{t,z:[K::ZERO;10],lambda,chi,theta:bat.theta,zc:bat.zerocheck_point,mu:bat.mu,eta,claim:w.v[0]};
    for r in 0..10 {
        let sent=&w.v[1+27*r..1+27*(r+1)];
        let mut record=vec![r as u8];record.extend(bytes(sent));
        s.t.absorb(label::V6_COMPACT_SEMANTIC_ROUND,&record);
        s.z[r]=sample(&mut s.t,false)?;
        if cache.is_empty() {
        let mut poly=[K::ZERO;28];poly[0]=sent[0];poly[2..].copy_from_slice(&sent[1..]);
        #[cfg(not(v8_semantic_boundary))]
        {poly[1]=s.claim.sub(poly[0].add(poly[0]).add(poly[2..].iter().copied().fold(K::ZERO,|a,b|a.add(b))));}
        #[cfg(v8_semantic_boundary)]
        {poly[1]=super::semantic_boundary::missing(s.claim,poly[0],poly[2..].try_into().unwrap());}
            #[cfg(not(v8_block_horner))] {s.claim=evaluate_state_only_polynomial(&poly,s.z[r]);}
            #[cfg(v8_block_horner)] {s.claim=semantic_eval(&poly,s.z[r]);}
        } else {
            // Cache is verifier-owned and freshly derived AFTER this round's challenge.
            #[cfg(not(target_os="solana"))] let old_claim=s.claim;
            s.claim=crate::r20_semantic_basis::evaluate_round(s.claim,sent.try_into().unwrap(),s.z[r],
                (&mut cache[1+27*r..1+27*(r+1)]).try_into().unwrap());
            #[cfg(not(target_os="solana"))] {
        let mut poly=[K::ZERO;28];poly[0]=sent[0];poly[2..].copy_from_slice(&sent[1..]);
        #[cfg(not(v8_semantic_boundary))]
        {poly[1]=old_claim.sub(poly[0].add(poly[0]).add(poly[2..].iter().copied().fold(K::ZERO,|a,b|a.add(b))));}
        #[cfg(v8_semantic_boundary)]
        {poly[1]=super::semantic_boundary::missing(old_claim,poly[0],poly[2..].try_into().unwrap());}
            assert_eq!(s.claim,evaluate_state_only_polynomial(&poly,s.z[r]));
            }
        }
    }
    if !cache.is_empty() {
        for r in (0..10).rev() {
            for v in &mut cache[1+27*r..1+27*(r+1)] {
                *v=crate::r20_semantic_basis::scale_power_of_two(*v,9-r);
            }
        }
        cache[0]=crate::r20_semantic_basis::scale_power_of_two(K::ONE,10);
        #[cfg(not(target_os="solana"))] {
            let mut original=vec![K::ZERO;271];
            crate::r18_sparse_coded_g::coin_weights_into(&s.z,&mut original);
            assert_eq!(cache,original.as_slice(),"actual ten-challenge G cache");
        }
    }
    checkpoint("v8:semantic-rounds");
    let claims:[K;84]=std::array::from_fn(|i|w.v[271+(i/28)*29+i%28]);
    let actual=payment_terminal(public,transition,&claims,&s.z,&s)?;
    if actual!=s.claim{return Err(Error::Terminal);}
    checkpoint("v8:semantic-terminal");
    #[cfg(v8_semantic_control)] {
        // Matched selected V7 terminal call: same literal 3x28 projection and
        // all public/challenge inputs. Diagnostic duplicate, NOT a saving.
        let again=payment_terminal(public,transition,&claims,&s.z,&s)?;
        if again!=actual{return Err(Error::Terminal);}
        checkpoint("v8:selected-semantic-control");
    }
    Ok(s)
}
#[cfg(v8_semantic_control)]
#[inline(never)]
fn selected_terminal_control(public:&PoolV1PrivateTransferPublicV1,transition:&PoolV1PairLatePublicStatementV1,claims:&[K;84],s:&row::Semantic)->Result<K,Error>{
    evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
        public,transition,claims,&s.z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta).map_err(|_|Error::Terminal)
}
/// Codes are research diagnostics, never production acceptance/status codes.
#[inline(never)]
fn semantic_bytes(w:&Wire<'_>,binding:&[u8;32],public:&[u8],transition:&[u8])->Result<row::Semantic,u32>{
    let public=decode_pool_v1_private_transfer_public_v1(public).map_err(|_|1u32)?;
    let transition=decode_pool_v1_pair_late_public_statement_v1(transition).map_err(|_|2u32)?;
    semantic(w,binding,&PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),&transition).map_err(|_|4u32)
}
#[cfg_attr(v8_semantic_stack,inline(never))]
pub(super) fn payment_terminal(public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1,claims:&[K;84],z:&[K;10],s:&row::Semantic)->Result<K,Error>{
    #[cfg(v8_positive_transfer)]
    if !matches!(public,PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)){return Err(Error::Shape);}
    let value=match public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>
            evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(p,transition,claims,z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta),
        PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>
            evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1(p,transition,claims,z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta),
    }.map_err(|_|Error::Terminal)?;
    let value=value.sub(claims[27].mul(corelib::state_only_hiding::state_only_explicit_g_mask_factor(z))).add(claims[27]);

    #[cfg(v8_positive_transfer)]
    return Ok(value.add(super::positive_transfer::terminal_delta(claims,z,s.theta,&s.zc,s.eta)));
    #[cfg(not(v8_positive_transfer))] Ok(value)
}
#[inline(never)]
pub fn verify(body:&[u8],binding:&[u8;32],public:&[u8],transition:&[u8])->Result<(),u32>{

#[cfg(target_os="solana")] { (); (); }
    checkpoint("v8:start");
    let w=parse(body).map_err(|_|3u32)?;
    checkpoint("v8:parse");
    let public=decode_pool_v1_private_transfer_public_v1(public).map_err(|_|1u32)?;
    let transition=decode_pool_v1_pair_late_public_statement_v1(transition).map_err(|_|2u32)?;
    verify_parsed(&w,binding,&PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),&transition)
}
/// Typed objects ONLY after the complete wrapper's canonical/account checks.
/// This removes encode/decode round-trips, not any untrusted-byte validation.
#[inline(never)]
pub fn verify_payment(body:&[u8],binding:&[u8;32],public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1)->Result<(),u32>{

#[cfg(target_os="solana")] { (); (); }
    checkpoint("v8:start");
    let w=parse(body).map_err(|_|3u32)?;
    checkpoint("v8:parse");
    verify_parsed(&w,binding,public,transition)
}
#[inline(never)]
fn verify_parsed(w:&Wire<'_>,binding:&[u8;32],public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1)->Result<(),u32>{

#[cfg(target_os="solana")] { (); (); }
    let mut semantic_basis=vec![K::ZERO;271];
    let s=semantic_cached(w,binding,public,transition,&mut semantic_basis).map_err(|_|4u32)?;
#[cfg(target_os="solana")] { (); (); }

    let prepared=crate::r17_relation::prepare_compact(s,w).map_err(|_|5u32)?;
#[cfg(target_os="solana")] { (); (); }

    let result=crate::r17_relation::verify_cached(w,prepared,false,Some(&semantic_basis));
    #[cfg(all(target_os="solana",r18_primary_only))]
    { return result.map_err(|_|6u32); }
    #[cfg(not(all(target_os="solana",r18_primary_only)))]
    {

#[cfg(target_os="solana")] { (); (); }
    let s=semantic(w,binding,public,transition).map_err(|_|4u32)?;
#[cfg(target_os="solana")] { (); (); }

    let prepared=crate::r17_relation::prepare(s,w).map_err(|_|5u32)?;
#[cfg(target_os="solana")] { (); (); }

    let reference=crate::r17_relation::verify(w,prepared,true);
    assert_eq!(result,reference,"R17 complete deferred/dense outcome");
    result.map_err(|_|6u32)
    }
}
