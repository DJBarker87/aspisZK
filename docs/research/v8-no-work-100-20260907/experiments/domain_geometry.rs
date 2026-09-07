//! Finite source-domain audit, not a universal Lean encoder refinement.
extern crate aspis_core;
use aspis_core::{circle_fri::selected_circle_fiber_points_shared, field::M31};
fn main() {
    let ids: Vec<u32> = (0..1 << 18).collect();
    let points = selected_circle_fiber_points_shared(20, &ids).unwrap();
    let mut line = Vec::with_capacity(points.len());
    for p in &points {
        assert_ne!(p.x, M31::ZERO);
        assert_ne!(p.y, M31::ZERO);
        assert_eq!(p.x.mul(p.x).add(p.y.mul(p.y)), M31::ONE);
        line.push(p.x.mul(p.x).double().sub(M31::ONE).0);
    }
    line.sort_unstable();
    assert!(line.windows(2).all(|v| v[0] != v[1]));
    // Natural line tensor basis phi_j=product_{bit s in j} T_{2^s}.
    // Check its degree index and nonzero leading coefficient in actual M31.
    for j in 0..256usize {
        let mut degree = 0;
        let mut leading = M31::ONE;
        for bit in 0..8 {
            if j & (1 << bit) != 0 {
                let d = 1 << bit;
                degree += d;
                for _ in 0..d-1 { leading = leading.double(); }
            }
        }
        assert_eq!(degree, j);
        assert_ne!(leading, M31::ZERO);
    }
    println!("PASS {} distinct actual final-domain points; all circle/nonzero-x/nonzero-y checks; 256 tensor degrees/leading coefficients", line.len());
}
