//! Exact checked dot using the new guarded scalar product, research candidate.
use aspis_core::field::{QM31 as K,P};
#[inline(never)]
pub(super) fn dot(left:&[K],right:&[K])->Option<K> {
    if left.len()!=right.len() || left.len()>4096 {return None;}
    let canonical=|v:&K|v.c0.a.0<P && v.c0.b.0<P && v.c1.a.0<P && v.c1.b.0<P;
    let mut total=K::ZERO;
    for(a,b)in left.iter().zip(right) {
        if !canonical(a)||!canonical(b){return None;}
        total=total.add(a.mul(*b));
    }
    Some(total)
}
