/// Checked boundary for a dot product. No caller canonicality assumption:
/// every operand is checked by r24_canonical_mul before it is consumed.
/// The original general QM31 API and its noncanonical fallback are unchanged.
#[inline(never)]
pub fn r25_checked_dot(left:&[QM31],right:&[QM31])->Option<QM31> {
    if left.len()!=right.len() || left.len()>4096 {return None;}
    let mut total=QM31::ZERO;
    for (&a,&b) in left.iter().zip(right) {
        let product=r24_canonical_mul(a,b)?;
        // The guarded product uses the existing canonical reducer for each
        // output limb. Inductively total is canonical as well. Thus every
        // sum here is <=2P-2<2^32; the cast follows the one subtraction.
        let add=|a:M31,b:M31| {
            let s=u64::from(a.0)+u64::from(b.0);
            M31((if s>=u64::from(P){s-u64::from(P)}else{s}) as u32)
        };
        total=QM31{c0:CM31::new(add(total.c0.a,product.c0.a),add(total.c0.b,product.c0.b)),
            c1:CM31::new(add(total.c1.a,product.c1.a),add(total.c1.b,product.c1.b))};
    }
    Some(total)
}
