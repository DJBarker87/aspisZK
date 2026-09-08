//! Shared host/SBF research verifier, public byte input only.
//! Does NOT authenticate caller/account context or settle a pool transaction.
use super::*;
use super::inactive_binding as row;
use aspis_statement::pool_v1::*;
use corelib::state_only_sumcheck::{begin_state_only_zerocheck,evaluate_state_only_polynomial};
use corelib::state_only_hiding::begin_state_only_masked_sumcheck;
#[cfg(v8_block_horner)]
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
pub(super) fn checkpoint(name:&str){
    #[cfg(all(v8_performance_sbf,not(v8_quiet_profile)))] {
        solana_program::msg!(name);
        solana_program::log::sol_log_compute_units();
    }
    #[cfg(any(not(v8_performance_sbf),v8_quiet_profile))] let _=name;
}
#[inline(never)]
fn semantic(w:&Wire<'_>,binding:&[u8;32],public:&PoolV1PrivateTransferPublicV1,transition:&PoolV1PairLatePublicStatementV1)->Result<row::Semantic,Error>{
    let mut t=Transcript::new(hash);
    t.absorb(label::PROFILE,b"AV8/payment-extraction/v1");
    t.absorb(label::STATEMENT,binding);t.absorb(label::ROOT,&w.roots.0);
    let lambda=sample(&mut t,false)?;let chi=sample(&mut t,false)?;
    t.absorb(label::SECOND_PHASE_ROOT,&w.roots.1);
    let bat=begin_state_only_zerocheck(&mut t).map_err(|_|Error::Sampler)?;
    let eta=begin_state_only_masked_sumcheck(&mut t,w.v[0]).map_err(|_|Error::Sampler)?;
    let mut s=row::Semantic{t,z:[K::ZERO;10],lambda,chi,theta:bat.theta,zc:bat.zerocheck_point,mu:bat.mu,eta,claim:w.v[0]};
    for r in 0..10 {
        let sent=&w.v[1+27*r..1+27*(r+1)];
        let mut poly=[K::ZERO;28];poly[0]=sent[0];poly[2..].copy_from_slice(&sent[1..]);
        poly[1]=s.claim.sub(poly[0].add(poly[0]).add(poly[2..].iter().copied().fold(K::ZERO,|a,b|a.add(b))));
        let mut record=vec![r as u8];record.extend(bytes(sent));
        s.t.absorb(label::V6_COMPACT_SEMANTIC_ROUND,&record);
        s.z[r]=sample(&mut s.t,false)?;
        #[cfg(not(v8_block_horner))] {s.claim=evaluate_state_only_polynomial(&poly,s.z[r]);}
        #[cfg(v8_block_horner)] {s.claim=semantic_eval(&poly,s.z[r]);}
    }
    checkpoint("v8:semantic-rounds");
    let claims:[K;84]=std::array::from_fn(|i|w.v[271+(i/28)*29+i%28]);
    let actual=evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
        public,transition,&claims,&s.z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta).map_err(|_|Error::Terminal)?;
    if actual!=s.claim{return Err(Error::Terminal);}
    checkpoint("v8:semantic-terminal");
    #[cfg(v8_semantic_control)] {
        // Matched selected V7 terminal call: same literal 3x28 projection and
        // all public/challenge inputs. Diagnostic duplicate, NOT a saving.
        let again=selected_terminal_control(public,transition,&claims,&s)?;
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
    semantic(w,binding,&public,&transition).map_err(|_|4u32)
}
#[inline(never)]
pub fn verify(body:&[u8],binding:&[u8;32],public:&[u8],transition:&[u8])->Result<(),u32>{
    checkpoint("v8:start");
    let w=parse(body).map_err(|_|3u32)?;
    checkpoint("v8:parse");
    let s=semantic_bytes(&w,binding,public,transition)?;
    #[cfg(not(v8_structured))]
    let(p,weights,claim,_)=row::prepare(s,&w,true).map_err(|_|5u32)?;
    #[cfg(v8_structured)]
    let(p,weights,claim,_)=row::structured::prepare(s,&w).map_err(|_|5u32)?;
    checkpoint("v8:ordinary-image-prepare");
    #[cfg(not(v8_structured))]
    row::relation(&w,p,weights,claim).map_err(|_|6u32)?;
    #[cfg(v8_structured)]
    {
        let result=row::structured::relation(&w,p,weights,claim);
        #[cfg(not(v8_performance_sbf))] {
            let s=semantic_bytes(&w,binding,public,transition)?;
            let(p,ordinary,c,_)=row::prepare(s,&w,true).map_err(|_|5u32)?;
            assert_eq!(result,row::relation(&w,p,ordinary,c),"complete dense-v2/structured outcome");
        }
        result.map_err(|_|6u32)?;
    }
    checkpoint("v8:relation-auth-terminal");
    Ok(())
}
