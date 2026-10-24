#![feature(stmt_expr_attributes, proc_macro_hygiene)]
#![allow(dead_code)]
extern crate alloc;
use aspis_core::{Digest32,field::{WideExact as E,QM31 as K},r0::CodeField};
use aspis_r1_cost_probe::{weights::{field,powers},verifier::Error};
pub use aspis_r1_cost_probe::{r1_semantic,trace};
pub mod fast_pairing;
fn prepared_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        #[cfg_attr(kani,kani::loop_invariant(proofs::outer_invariant(kani::index,&parts)))]
        for point in 0usize..6usize {
            let mut dot=crate::fast_pairing::EbyKDot::new();
            #[cfg_attr(kani,kani::loop_invariant(proofs::inner_invariant(point,kani::index,&dot)))]
            for l in 0usize..29usize {
                let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
                dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
            }
            parts[point+1]=dot.finish();
        }
        let mut claim=E::ZERO;
        #[cfg_attr(kani,kani::loop_invariant(proofs::sum_invariant(kani::index,claim)))]
        for i in 0usize..7usize {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
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
        #[cfg_attr(kani,kani::loop_invariant(proofs::sum_invariant(kani::index,claim)))]
        for i in 0usize..7usize {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        claim
}
fn prepared_claim_dot<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize)->Result<E,Error> {
    let mut dot=crate::fast_pairing::EbyKDot::new();
    #[cfg_attr(kani,kani::loop_invariant(proofs::inner_invariant(point,kani::index,&dot)))]
            for l in 0usize..29usize {
        let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
        dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
    }
    Ok(dot.finish())
}
fn fission_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        #[cfg_attr(kani,kani::loop_invariant(proofs::outer_invariant(kani::index,&parts)))]
        for point in 0usize..6usize {
            parts[point+1]=prepared_claim_dot(sem,y1,g,point)?;
        }
        Ok(prepared_claim_sum(k,parts))
}
#[cfg(kani)] mod proofs;
fn original_point_step<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize,parts:&mut[E;7])->Result<(),Error> {

            let mut dot=crate::fast_pairing::EbyKDot::new();
            #[cfg_attr(kani,kani::loop_invariant(proofs::inner_invariant(point,kani::index,&dot)))]
            for l in 0usize..29usize {
                let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
                dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
            }
            parts[point+1]=dot.finish();
        
 Ok(())
}
fn reference_point_step<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize,parts:&mut[E;7])->Result<(),Error> {
 parts[point+1]=prepared_claim_dot(sem,y1,g,point)?;
 Ok(())
}
fn owned_scalar(claims:&[[K;29];3],extra:&[K;29],before_z1:&[K;29],y1:&[u8],point:usize,l:usize)->K { match point {0..=2=>claims[point][l],3=>extra[l],4=>before_z1[l],_=>field(y1,l).c0()} }
fn owned_push(mut dot:crate::fast_pairing::EbyKDot,g:&[E;29],l:usize,scalar:K)->(Result<(),()>,crate::fast_pairing::EbyKDot) { let r=dot.push(g[l],scalar); (r,dot) }
fn owned_sum(k:&[E;7],parts:&[E;7])->E {         let mut claim=E::ZERO;
        #[cfg_attr(kani,kani::loop_invariant(proofs::sum_invariant(kani::index,claim)))]
        for i in 0usize..7usize {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        claim }
fn owned_claim_loops(claims:[[K;29];3],extra:[K;29],before_z1:[K;29],y1:&[u8],inactive:E,g:[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        #[cfg_attr(kani,kani::loop_invariant(proofs::outer_invariant(kani::index,&parts)))]
        for point in 0usize..6usize {
            let mut dot=crate::fast_pairing::EbyKDot::new();
            #[cfg_attr(kani,kani::loop_invariant(proofs::inner_invariant(point,kani::index,&dot)))]
            for l in 0usize..29usize {
                let scalar=owned_scalar(&claims,&extra,&before_z1,y1,point,l);
                let (r,next)=owned_push(dot,&g,l,scalar);dot=next;if r.is_err() { return Err(Error::Parse); }
            }
            parts[point+1]=dot.finish();
        }
        Ok(owned_sum(&k,&parts))
}
pub fn prepared_claim_owned<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> { owned_claim_loops(*sem.claims,sem.extra,sem.before_z1,y1,inactive,*g,kappa) }

fn owned_step<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize,l:usize,dot:crate::fast_pairing::EbyKDot)->(Result<(),Error>,crate::fast_pairing::EbyKDot) {
 let scalar=owned_scalar(&*sem.claims,&sem.extra,&sem.before_z1,y1,point,l);
 let (r,dot)=owned_push(dot,g,l,scalar);
 (r.map_err(|_|Error::Parse),dot)
}
