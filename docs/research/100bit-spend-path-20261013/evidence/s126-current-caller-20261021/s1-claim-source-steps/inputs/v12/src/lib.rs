#![allow(dead_code)]
extern crate alloc;
use aspis_core::{Digest32,field::{WideExact as E,QM31 as K},r0::CodeField};
use aspis_r1_cost_probe::{weights::{field,powers},verifier::Error};
pub use aspis_r1_cost_probe::{r1_semantic,trace};
pub mod fast_pairing;
fn prepared_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        for point in 0..6 {
            let mut dot=crate::fast_pairing::EbyKDot::new();
            for l in 0..29 {
                let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
                dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
            }
            parts[point+1]=dot.finish();
        }
        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        Ok(claim)
}
fn scalar_helper<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],point:usize,l:usize)->K { match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()} }
fn original_step<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize,l:usize,dot:&mut crate::fast_pairing::EbyKDot)->Result<(),Error> {
let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
 dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
 Ok(())
}
fn helper_step<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize,l:usize,dot:&mut crate::fast_pairing::EbyKDot)->Result<(),Error> {
 let scalar=scalar_helper(sem,y1,point,l);
 dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
 Ok(())
}

fn prepared_claim_sum(k:[E;7],parts:[E;7])->E {
        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        claim
}
fn prepared_claim_dot<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize)->Result<E,Error> {
    let mut dot=crate::fast_pairing::EbyKDot::new();
    for l in 0..29 {
        let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
        dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
    }
    Ok(dot.finish())
}
fn fission_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        for point in 0..6 {
            parts[point+1]=prepared_claim_dot(sem,y1,g,point)?;
        }
        Ok(prepared_claim_sum(k,parts))
}
#[cfg(kani)] mod proofs;
