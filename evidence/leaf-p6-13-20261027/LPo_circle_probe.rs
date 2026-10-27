#[path="LPo_native_field.rs"] mod field;
#[path="LPo_src/crates/aspis-core/src/circle.rs"] mod circle;
use field::{QM31, CM31};
use circle::{secure_ood_circle_point_from_parameter, SecureCirclePoint};
pub const CIRCLE_FALLBACK_PARAMETERS: [QM31; 2] = [
    QM31 {
        c0: crate::field::CM31::ZERO,
        c1: crate::field::CM31::ONE,
    },
    QM31 {
        c0: crate::field::CM31::ONE,
        c1: crate::field::CM31::ONE,
    },
];

/// The fallback circle point for OOD row `sample` (0 or 1): the image of
/// [`CIRCLE_FALLBACK_PARAMETERS`] under the secure rational map. The map
/// cannot fail on these parameters (`c1 ≠ 0`), so the unwrap is total; it is
/// written as an explicit match to keep this crate panic-free in practice.
pub fn circle_fallback_point(sample: usize) -> SecureCirclePoint {
    let parameter = CIRCLE_FALLBACK_PARAMETERS[sample % 2];
    match secure_ood_circle_point_from_parameter(parameter) {
        Ok(point) => point,
        // Unreachable: `c1 = 1 ≠ 0` for both parameters.
        Err(_) => SecureCirclePoint {
            x: QM31::ONE,
            y: QM31::ZERO,
        },
    }
}


// Literal control-flow counterpart of the retained Lean LPo_qpow, including
// the predecessor binder in the n+1 arm. Arithmetic is actual frozen field.rs.
fn model_pow(x:QM31,m:u128)->QM31 {
    if m==0 { return QM31::ONE; }
    let n=m-1;let y=model_pow(x,n/2);let z=y.mul(y);
    if n%2==0 { z.mul(x) } else { z }
}
fn model_point(t:QM31)->SecureCirclePoint {
    let square=t.mul(t);let den=QM31::ONE.add(square);
    let inv=model_pow(den,2147483647u128.pow(4)-2);
    SecureCirclePoint{x:QM31::ONE.sub(square).mul(inv),y:t.add(t).mul(inv)}
}
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn main(){
    for row in 0..2 {
        let t=std::hint::black_box(CIRCLE_FALLBACK_PARAMETERS[row]);
        let actual=secure_ood_circle_point_from_parameter(t).unwrap();
        assert_eq!(actual,circle_fallback_point(row));
        let model=model_point(t);
        println!("row={} native_x={:?} native_y={:?} retained_model_x={:?} retained_model_y={:?} equal={}",row,words(actual.x),words(actual.y),words(model.x),words(model.y),actual==model);
        assert_ne!(actual,model,"expected inverse-reference obstruction");
    }
}
