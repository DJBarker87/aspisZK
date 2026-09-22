//! R21 host-only public arithmetic trace driver.
//!
//! The source modules below are included by path and are intentionally not
//! copied or rewritten.  This binary is only a DAG extractor/evaluator; it is
//! not a verifier, proof system, or security argument.
extern crate aspis_core as native_core;
mod r21_trace_field;
use r21_trace_field::{K, M31};
use r21_trace_field as corelib;

#[path = "r17_basis_tables.rs"] mod r17_basis_tables;
mod basis_transport {
    use super::{K, M31};
    pub const N: usize = 1024;
    pub const PIVOT: usize = 1023;
    pub struct Transport { pub(crate) order: [usize; N], pub(crate) inactive: [bool; N] }
    pub trait Scalar: Copy { const ZERO: Self; fn plus(self, rhs: Self) -> Self; fn minus(self, rhs: Self) -> Self; }
    impl Scalar for K { const ZERO: Self = K::ZERO; fn plus(self,rhs:Self)->Self {self.add(rhs)} fn minus(self,rhs:Self)->Self {self.sub(rhs)} }
    impl Scalar for M31 { const ZERO: Self = M31::ZERO; fn plus(self,rhs:Self)->Self {self.add(rhs)} fn minus(self,rhs:Self)->Self {self.sub(rhs)} }
    static T: Transport = Transport { order: super::r17_basis_tables::ORDER, inactive: super::r17_basis_tables::INACTIVE };
    pub fn transport() -> &'static Transport { &T }
    impl Transport {
        pub fn dual<F: Scalar>(&self, w: &[F]) -> Vec<F> { assert_eq!(w.len(),N); self.order.iter().map(|&r| if r != PIVOT && self.inactive[r] { w[r].minus(w[PIVOT]) } else { w[r] }).collect() }
        pub fn forward<F: Scalar>(&self, m: &[F]) -> Vec<F> { assert_eq!(m.len(),N); let mut out=self.order.iter().map(|&r|m[r]).collect::<Vec<_>>(); out[PIVOT]=self.inactive.iter().enumerate().fold(F::ZERO,|s,(r,&inactive)|if inactive{s.plus(m[r])}else{s}); out }
        pub fn inverse<F: Scalar>(&self, t: &[F]) -> Vec<F> { assert_eq!(t.len(),N); let mut m=vec![F::ZERO;N]; for (j,&r) in self.order.iter().enumerate(){m[r]=t[j];} let s=self.inactive.iter().enumerate().filter(|(r,&i)|i&&*r!=PIVOT).fold(F::ZERO,|s,(r,_)|s.plus(m[r])); m[PIVOT]=t[PIVOT].minus(s); m }
    }
}
#[path = "r17_weighted_groups.rs"] mod r17_weighted_groups;
#[path = "r19_channel_ordinary.rs"] mod r19_channel_ordinary;

fn image_terminal(t: K, b: K, c: K, a: [K; 4]) -> K {
    let a0 = a[0];
    a[1].mul(a[2]).mul(a[3]).mul(
        t.mul(a0).add(t.square().mul(b.mul(a0.square())
            .sub(c.mul(a0.square().mul(a0)))))
    ).mul_m31(M31(8_388_608))
}

fn write_json_string(s: &mut String, x: &str) {
    s.push('"');
    for c in x.chars() { match c { '"' => s.push_str("\\\""), '\\' => s.push_str("\\\\"), _ => s.push(c) } }
    s.push('"');
}

fn emit_json(output: K, input_count: usize) {
    let nodes = corelib::nodes();
    let mut s = String::from("{\"input_count\":"); s.push_str(&input_count.to_string());
    s.push_str(",\"output\":"); s.push_str(&output.0.to_string()); s.push_str(",\"nodes\":[");
    for (i,n) in nodes.iter().enumerate() {
        if i != 0 { s.push(','); }
        s.push('{');
        match *n {
            corelib::Node::Input(x) => { s.push_str("\"op\":\"input\",\"index\":"); s.push_str(&x.to_string()); }
            corelib::Node::Const(c) => { s.push_str("\"op\":\"const\",\"constant\":["); for j in 0..4 { if j!=0{s.push(',');} s.push_str(&c[j].to_string()); } s.push(']'); }
            corelib::Node::Add(a,b) => { s.push_str("\"op\":\"add\",\"args\":["); s.push_str(&a.to_string()); s.push(','); s.push_str(&b.to_string()); s.push(']'); }
            corelib::Node::Mul(a,b) => { s.push_str("\"op\":\"mul\",\"args\":["); s.push_str(&a.to_string()); s.push(','); s.push_str(&b.to_string()); s.push(']'); }
            corelib::Node::Sub(a,b) => { s.push_str("\"op\":\"sub\",\"args\":["); s.push_str(&a.to_string()); s.push(','); s.push_str(&b.to_string()); s.push(']'); }
        }
        s.push('}');
    }
    s.push_str("]}\n"); print!("{s}");
}

fn main() {
    corelib::reset();
    let x: [K; 24] = core::array::from_fn(K::input);
    let audit: [K; 11] = x[..11].try_into().unwrap();
    let abc: [K; 3] = x[11..14].try_into().unwrap();
    let alpha: [K; 4] = x[14..18].try_into().unwrap();
    let beta = x[18];
    let finals: [K; 4] = x[19..23].try_into().unwrap();
    let tau = x[23];
    let mut workspace = vec![K::ZERO; 1024];
    let kernel = r17_weighted_groups::Kernel::new(abc, alpha);
    let ordinary = r19_channel_ordinary::terminal_shared(&audit, abc, alpha, beta, &mut workspace, &kernel);
    let ordinary_scalar = corelib::field::qm31_sum_products4(ordinary, finals);
    let image = (K::ONE.sub(beta).add(beta.mul(tau.square())))
        .mul(image_terminal(tau, abc[1], abc[2], alpha)).mul(finals[3]);
    emit_json(ordinary_scalar.add(image), 24);
}
