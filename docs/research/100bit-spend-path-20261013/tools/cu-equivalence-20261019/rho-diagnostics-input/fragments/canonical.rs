#[inline(always)]
fn canonical_qm31(value: QM31) -> QM31 {
    let reduce = |x: M31| M31(x.0 % P);
    QM31 {
        c0: CM31 {
            a: reduce(value.c0.a),
            b: reduce(value.c0.b),
        },
        c1: CM31 {
            a: reduce(value.c1.a),
            b: reduce(value.c1.b),
        },
    }
}