#!/usr/bin/env python3
"""X1 stage 2, item B: CM31::inv without the function passed by value. Same field operations in the same order
(norm = a*a + b*b; one M31::inv of the norm; a*inv; (-b)*inv). inv_with is unchanged (still used by
cm31_batch_inverse_with). A differential test keeps the old body (inv_with(M31::inv)) under cfg(test)."""
import sys
from pathlib import Path
T = Path(sys.argv[1]); assert 'src-frz-a' not in str(T)
p = T / 'crates/aspis-core/src/field.rs'; t = p.read_text()
old = '''    /// Inverse via conjugate/norm: one M31 inversion + a few muls.
    pub fn inv(self) -> CM31 {
        self.inv_with(M31::inv)
    }
'''
new = '''    /// Inverse via conjugate/norm: one M31 inversion + a few muls.
    /// The body of `inv_with` with `M31::inv` written in place of the injected backend (the translator cannot take
    /// a function as a value): the same field operations in the same order.
    pub fn inv(self) -> CM31 {
        let norm = self.a.mul(self.a).add(self.b.mul(self.b));
        let inv_norm = norm.inv();
        CM31 {
            a: self.a.mul(inv_norm),
            b: self.b.neg().mul(inv_norm),
        }
    }
'''
assert t.count(old) == 1; t = t.replace(old, new)
t += '''
/// X1 rewrite of `CM31::inv`: differential check against the frozen body (3d700effcab field.rs 390-392).
#[cfg(test)]
mod x1_cm31_inv_rewrite {
    extern crate std;
    use super::*;
    use std::panic::catch_unwind;

    /// The frozen body of `CM31::inv`: the base-field inversion passed by value to `inv_with`.
    fn old_inv(x: CM31) -> CM31 {
        x.inv_with(M31::inv)
    }

    fn payload(e: std::boxed::Box<dyn core::any::Any + Send>) -> std::string::String {
        e.downcast_ref::<&str>().map(|s| std::string::ToString::to_string(s))
            .or_else(|| e.downcast_ref::<std::string::String>().cloned()).unwrap_or_default()
    }

    /// Same value, or the same panic message.
    fn same(x: CM31) {
        match (catch_unwind(|| x.inv()), catch_unwind(|| old_inv(x))) {
            (Ok(a), Ok(b)) => assert_eq!(a, b, "{x:?}"),
            (Err(a), Err(b)) => assert_eq!(payload(a), payload(b), "{x:?}"),
            (a, b) => panic!("panic behaviour differs at {x:?}: new ok {} old ok {}", a.is_ok(), b.is_ok()),
        }
    }

    #[test]
    fn vectors_edges_and_random() {
        // the existing inverse test vectors (m31_inverse, m31_inverse_addition_chain_matches_fermat_pow, cm31_field_axioms)
        let mut values = std::vec![0u32, 1, 2, 3, 12345, P / 2, P - 2, P - 1, 0x4000_0000, 123456789, 987654321, 555, 777777];
        let mut state = 0x243f_6a88_85a3_08d3u64;
        for _ in 0..64 {
            state = state.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
            values.push((state % u64::from(P)) as u32);
        }
        for &a in &values {
            for &b in &values {
                same(CM31::new(M31(a), M31(b)));
            }
        }
        for _ in 0..1 << 16 {
            state = state.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
            same(CM31::new(M31((state % u64::from(P)) as u32), M31(((state >> 32) % u64::from(P)) as u32)));
        }
        // zero: both panic in M31::inv with "inverse of zero"
        same(CM31::ZERO);
    }

    /// Exhaustive over the base line: (v, 0) and (0, v) for every nonzero v, so every nonzero M31 value goes through
    /// M31::inv on both paths. Run in release: cargo test --release -p aspis-core --lib x1_cm31_inv_rewrite -- --ignored
    #[test]
    #[ignore]
    fn exhaustive_base_line() {
        let threads: std::vec::Vec<_> = (0..4u32)
            .map(|k| std::thread::spawn(move || {
                let mut v = 1 + k;
                while v < P {
                    let x = M31(v);
                    assert_eq!(CM31::new(x, M31::ZERO).inv(), old_inv(CM31::new(x, M31::ZERO)), "{v}");
                    assert_eq!(CM31::new(M31::ZERO, x).inv(), old_inv(CM31::new(M31::ZERO, x)), "{v}");
                    v += 4;
                }
            }))
            .collect();
        for t in threads { t.join().unwrap(); }
    }
}
'''
p.write_text(t); print('ok')
