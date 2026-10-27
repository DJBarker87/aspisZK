//! Proof tooling only: test the unrestricted op121 P6 Horner-reference ROW.
use aspis_core::field::{QM31,CM31,M31,P};
use aspis_core::state_only_sumcheck::{evaluate_state_only_polynomial as source,
    evaluate_state_only_polynomial_horner as reference};
fn q(w: [u32;4]) -> QM31 {QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
fn raw(v: QM31)->[u32;4] {[v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0]}
fn check(p: [QM31;28],x:QM31,case:usize) {
    let a=source(&p,x);let b=reference(&p,x);
    if a!=b {
        println!("COUNTEREXAMPLE case={case} x={:?} source={:?} reference={:?}",raw(x),raw(a),raw(b));
        for (i,c) in p.iter().enumerate() {if *c!=QM31::ZERO {println!("coefficient[{i}]={:?}",raw(*c));}}
        std::process::exit(42);
    }
}
fn main() {
    let edges=[0,1,P-1,P,P+1,u32::MAX-1,u32::MAX];let mut case=0;
    for e in edges {for f in edges {for i in 0..28 {for lane in 0..4 {
        let mut word=[0;4];word[lane]=e;
        let mut p=[QM31::ZERO;28];p[i]=q(word);
        for ch in [[f,0,0,0],[0,f,0,0],[0,0,f,0],[0,0,0,f],[f;4]] {
            check(p,q(ch),case);case+=1;
        }
    }}}}
    println!("checked {case} sparse boundary cases; no counterexample");
}
