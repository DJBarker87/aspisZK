//! Same prepared affine kernel as baseline affine_primal::fold, owned storage.
use super::corelib::field::{QM31 as K,PreparedQm31Multiplier as P,qm31_add_sum_products3_prepared};
pub(super) fn fold(mut v:Vec<K>,a:K)->Vec<K> {
    let a2=a.square();let ps=[P::new(a),P::new(a2),P::new(a2.mul(a))];
    let n=v.len()/4;
    for i in 0..n {
        // Read the complete old block before writing its lower output slot.
        let value=qm31_add_sum_products3_prepared(v[4*i],&ps,&[v[4*i+1],v[4*i+2],v[4*i+3]]);
        v[i]=value;
    }
    v.truncate(n);
    v
}
