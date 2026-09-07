//! Research-only image-aware relation execution; no production entry point.
//! Uses the pinned production QM31 kernel. Challenges are explicit IDEAL inputs;
//! no fake hash function, no FS/CU claim and no authenticated query claim.
#![allow(dead_code)]
extern crate alloc;
#[path = "../../../../crates/aspis-core/src/field.rs"] mod field;
#[path = "../../../../crates/aspis-core/src/circle.rs"] mod circle;
#[path = "../../../../crates/aspis-core/src/transcript.rs"] mod transcript;
// Only transcript.rs's unused diagnostic KATs reference this wire-size name.
// Exact sumcheck.rs constant; no sumcheck arithmetic is stubbed or imported.
mod sumcheck { pub const SUMCHECK_BYTES:usize=7*16; }
use field::{CM31, M31, QM31 as K};

/// Proposed exact research framing, NOT registered as a production profile.
/// Caller must already bind the statement/roots/OOD/ordinary claims and freeze
/// all data determining Q,w,C; call BEFORE requesting/absorbing response zero.
/// This helper is type-checked but not used by the ideal-input tests below.
fn derive_image_tau(t:&mut transcript::Transcript)->Result<K,transcript::ChallengeSampleExhausted> {
    t.absorb(transcript::label::PROFILE,b"aspis-v8-image-gate-v1");
    t.challenge_nonzero_qm31()
}

fn scalar(v:u32)->K { K::from_cm31(CM31::new(M31(v),M31::ZERO)) }
fn sample(v:u32)->K { K { c0:CM31::new(M31(v),M31(v+1)),c1:CM31::new(M31(v+2),M31(v+3)) } }
fn dot(a:&[K],b:&[K])->K { assert_eq!(a.len(),b.len()); a.iter().zip(b).fold(K::ZERO,|s,(a,b)|s.add(a.mul(*b))) }
fn eval(a:&[K],x:K)->K { a.iter().rev().fold(K::ZERO,|s,c|s.mul(x).add(*c)) }
fn primal(v:&[K],a:K)->Vec<K> { v.chunks_exact(4).map(|v|eval(v,a)).collect() }
fn dual(v:&[K],a:K)->Vec<K> {
    let a2=a.square();let a3=a2.mul(a);
    v.chunks_exact(4).map(|v|v[0].add(a3.mul(v[1])).add(a2.mul(v[2])).add(a.mul(v[3])).half().half()).collect()
}
fn honest(v:&[K],w:&[K])->[K;7] {
    let mut p=[K::ZERO;7];
    for (v,w) in v.chunks_exact(4).zip(w.chunks_exact(4)) {
        let d=[w[0],w[3],w[2],w[1]].map(|w|w.half().half());
        for i in 0..4 { for j in 0..4 {p[i+j]=p[i+j].add(v[i].mul(d[j]));} }
    }
    assert_eq!(p[0].add(p[4]).mul(scalar(4)),dot(v,w));p
}
// Exact compact source reconstruction: six transmitted values, c4 omitted.
fn reconstruct(sent:[K;6],claim:K)->[K;7] {
    [sent[0],sent[1],sent[2],sent[3],claim.half().half().sub(sent[0]),sent[4],sent[5]]
}
fn transmitted(p:[K;7])->[K;6] { [p[0],p[1],p[2],p[3],p[5],p[6]] }
fn image(q:&[K],b:K,c:K)->[K;2] { [q[1023],b.mul(q[1022]).sub(c.mul(q[1021]))] }
fn image_weights(t:K,b:K,c:K)->Vec<K> {
    let mut w=vec![K::ZERO;1024]; w[1023]=t; w[1022]=t.square().mul(b);w[1021]=t.square().mul(c).neg();w
}
fn compact(t:K,b:K,c:K,a:[K;4])->[K;4] {
    let a02=a[0].square();let a03=a02.mul(a[0]);
    let inner=t.mul(a[0]).add(t.square().mul(b.mul(a02).sub(c.mul(a03))));
    let out=a[1].mul(a[2]).mul(a[3]).mul(inner).mul_m31(M31(8_388_608)); // 256^-1 mod p
    [K::ZERO,K::ZERO,K::ZERO,out]
}
// Immutable data before tau; the image weights are installed BEFORE any
// first-round response is obtained. Real integration must derive tau from the
// transcript after a fresh domain-separation record, not accept it from a proof.
struct Frozen { q:Vec<K>,w:Vec<K>,claim:K,b:K,c:K }
struct Mixed { q:Vec<K>,w:Vec<K>,claim:K }
impl Frozen {
    fn mix(self,tau:K)->Mixed {
        assert_ne!(tau,K::ZERO);
        let iw=image_weights(tau,self.b,self.c);
        let w=self.w.iter().zip(iw).map(|(w,i)|w.add(i)).collect();
        Mixed{q:self.q,w,claim:self.claim}
    }
}

fn main() {
    assert_eq!(M31(8_388_608).mul(M31(256)),M31::ONE);
    let mut terminals=0;let mut rounds=0;let mut collision_accepts=0;
    for case in 0..80u32 {
        let t=sample(13+case);let b=sample(113+case);let c=sample(213+case);
        let mut a=[sample(313+case),sample(413+case),sample(513+case),sample(613+case)];
        if case<4 {a[case as usize]=K::ZERO;} if (4..8).contains(&case) {a[(case-4) as usize]=K::ONE;}
        let mut dense=image_weights(t,b,c);for x in a {dense=dual(&dense,x);}
        assert_eq!(dense,compact(t,b,c,a));terminals+=4;
        let q:Vec<K>=(0..1024).map(|i|sample(1024+case+i)).collect();
        let w:Vec<K>=(0..1024).map(|i|sample(4096+case+i)).collect();
        let prior=sample(9000+case);let e=image(&q,b,c);
        let claim=dot(&q,&w).add(prior);
        let mixed=Frozen{q,w,claim,b,c}.mix(t);
        assert_eq!(mixed.claim.sub(dot(&mixed.q,&mixed.w)),prior.sub(t.mul(e[0])).sub(t.square().mul(e[1])));
        let mut q=mixed.q;let mut w=mixed.w;let mut claim=mixed.claim;
        let mut had_repair=false;
        for (round,alpha) in a.into_iter().enumerate() {
            let before=claim.sub(dot(&q,&w));let h=honest(&q,&w);
            let mut sent=transmitted(h);
            // Responses really adapt to previous claim/challenges. This is one
            // tested strategy, not enumeration of all causal strategies.
            if case%2==1 {sent[1]=sent[1].add(claim.mul(scalar(round as u32+1)));}
            let p=reconstruct(sent,claim);let delta:Vec<K>=p.iter().zip(h).map(|(p,h)|p.sub(h)).collect();
            assert_eq!(delta[0].add(delta[4]).mul(scalar(4)),before);
            claim=eval(&p,alpha);q=primal(&q,alpha);w=dual(&w,alpha);
            let after=claim.sub(dot(&q,&w));assert_eq!(after,eval(&delta,alpha));
            had_repair |= before!=K::ZERO && after==K::ZERO;
            if round==0 {
                // F=F*: all pointwise residuals zero; Tag-73's shifted query
                // addition preserves discrepancy for every nonzero rho.
                let rho=sample(15000+case);let mut rpow=rho;
                let old=claim.sub(dot(&q,&w));
                for index in 0..22 {
                    // Generic checked linear evaluation covectors; this is not
                    // a claim that these are authenticated circle queries.
                    let ew:Vec<K>=(0..256).map(|j|scalar(1+((j+index)%13) as u32)).collect();
                    let value=dot(&q,&ew);claim=claim.add(rpow.mul(value));
                    for j in 0..256 {w[j]=w[j].add(rpow.mul(ew[j]));}rpow=rpow.mul(rho);
                }
                assert_eq!(old,claim.sub(dot(&q,&w)));
            }
            rounds+=1;
        }
        if claim==dot(&q,&w) {assert!(had_repair);collision_accepts+=1;}
    }
    for a in [K::ZERO,K::ONE,sample(19),sample(71)] {
        let delta=[a.square().mul(a).neg(),K::ZERO,K::ZERO,K::ONE];
        assert_eq!(primal(&delta,a),[K::ZERO]);assert_eq!(delta[3],K::ONE);
    }
    // Image-valid controls stay admitted: a nonzero q with both image zeros.
    for c in 0..12 {let mut q=vec![K::ZERO;1024];q[c]=sample(c as u32+1);assert_eq!(image(&q,sample(11),sample(29)),[K::ZERO;2]);}
    println!("PASS {terminals} terminal values; {rounds} source-shaped adaptive relation round identities; 80 exact query-injection discrepancy identities");
    println!("PASS 4 final-only kernel counterexamples; 12 image-valid controls; {collision_accepts} terminal collisions explained by a named repair");
    println!("Research-only ideal challenge inputs: no complete V8 verifier, FS, authentication, privacy or CU claim.");
}
