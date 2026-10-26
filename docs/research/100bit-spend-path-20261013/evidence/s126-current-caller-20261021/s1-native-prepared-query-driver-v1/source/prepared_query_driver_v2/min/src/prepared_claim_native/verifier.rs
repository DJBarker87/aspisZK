use aspis_core::r0::CodeField;
use alloc::{boxed::Box,vec::Vec};
use aspis_core::{Digest32,field::{WideExact as E,QM31 as K},circle::SecureCirclePoint};
use crate::{transport::Variant,weights::{field,powers},transcript::Transcript};
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation,
    /// Host prover only (LOG D38.3): this attempt's challenges fail the public
    /// P_R1 check. Carries no challenge and no conjunct.
    #[cfg(feature="prover")] Rejected,
    /// Host prover only (D38.3): all N = 8 attempts were rejected; nothing is published.
    #[cfg(feature="prover")] AttemptsExhausted,
    /// Host prover only: the operating-system entropy source failed.
    #[cfg(feature="prover")] Entropy }
pub struct View<'a> {
    pub variant:Variant,pub semantic:&'a[u8],pub y1:&'a[u8],pub inactive:E,
    pub round0:&'a[u8],pub folded_root:Option<&'a[u8;32]>,pub round1:&'a[u8],
    pub final_message:&'a[u8],pub query_bytes:&'a[u8],
}
pub struct Prepared {
    pub variant:Variant,pub roots:[[u8;32];2],pub gamma:E,pub kappa:E,pub alpha:[E;2],pub rho:K,
    pub queries:[u32;22],pub semantic_alpha:[K;10],pub z:[SecureCirclePoint;2],pub claim:E,pub state:[u8;32],
}
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
impl Prepared {
    #[inline(never)]
    pub fn new<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<'_>,hash:H,g:&mut [E;29])->Result<Box<Self>,Error> {
        let mut t=Transcript::new(hash,sem.transcript.state(),v.variant);
        let gamma=t.scalar(27,v.y1,true);
        let kappa=t.scalar(28,&v.inactive.to_le_bytes(),false);
        let alpha0=t.scalar(29,v.round0,false);
        let (alpha,row)=if v.variant.folds()==2 {
            let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);
            ([alpha0,t.scalar(30,&bytes,false)],31)
        } else {
            ([alpha0,E::ZERO],30)
        };
        let queries=t.queries(row,v.final_message)?;
        let rho=t.scalar_k(row+1,&[]);
        // Reuse this caller-owned scratch array in tx1; it is never serialized.
        *g=powers::<29>(gamma);
        let claim=prepared_claim(sem,v.y1,v.inactive,g,kappa)?;
        Ok(Box::new(Self{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}))
    }
}

#[cfg(kani)]
#[path="proofs.rs"]mod proofs;
