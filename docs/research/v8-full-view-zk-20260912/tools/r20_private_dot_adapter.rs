//! Private canonical packet arithmetic, with checked Aspis-QM31 entry/exit.
//! No public field API is changed. Conversion is once per input operand.
#[path="r20_private_canonical.rs"]
mod canonical;
#[path="r20_private_dot.rs"]
mod whole_dot;
use aspis_core::field::{QM31 as K,CM31,M31};

#[inline(never)]
pub(super) fn dot(left:&[K],right:&[K])->Option<K> {
    if left.len()!=right.len() || left.len()>whole_dot::MAX_TERMS {return None;}
    let mut sum=whole_dot::Dot::new();
    for (a,b) in left.iter().zip(right) {
        let cv=|q:&K|canonical::Q::from_limbs([q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]);
        sum.push(cv(a)?,cv(b)?).ok()?;
    }
    let [a,b,c,d]=sum.finish().limbs();
    Some(K{c0:CM31::new(M31(a),M31(b)),c1:CM31::new(M31(c),M31(d))})
}
