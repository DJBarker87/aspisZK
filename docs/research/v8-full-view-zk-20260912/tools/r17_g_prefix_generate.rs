//! Optimized host generator for the 1024-point, degree-<479 G prefix.
//!
//! This intentionally derives the denominator inverse independently from the
//! retained 2048-point generator.  It emits only the first 479 coefficients
//! into a zero-padded 1024-point spectrum; no mask, challenge, or degree is
//! introduced by this experiment.
extern crate aspis_core;
use aspis_core::field::{CM31, M31};

fn fft1024(a: &mut [CM31], roots: &[CM31]) {
    assert_eq!(a.len(), 1024);
    let mut j = 0;
    for i in 1..1024 {
        let mut bit = 512;
        while j & bit != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j ^= bit;
        if i < j {
            a.swap(i, j);
        }
    }
    let mut len = 2;
    while len <= 1024 {
        let step = 1024 / len;
        for start in (0..1024).step_by(len) {
            for k in 0..len / 2 {
                let u = a[start + k];
                let v = a[start + k + len / 2].mul(roots[k * step]);
                a[start + k] = u.add(v);
                a[start + k + len / 2] = u.sub(v);
            }
        }
        len *= 2;
    }
}

fn main() {
    let root = CM31::new(M31(2), M31(1268011823)).pow(1 << 21);
    assert_eq!(root.pow(1024), CM31::ONE);
    assert_ne!(root.pow(512), CM31::ONE);
    let mut roots = vec![CM31::ONE; 1024];
    for i in 1..1024 {
        roots[i] = roots[i - 1].mul(root);
    }

    // Product tree for exactly the retained 271 nodes.
    let mut tree = vec![Vec::<M31>::new(); 1024];
    for i in 0..512 {
        tree[512 + i] = if i < 271 {
            vec![M31::ONE, M31((i + 1) as u32).neg()]
        } else {
            vec![M31::ONE]
        };
    }
    for i in (1..512).rev() {
        let mut d = vec![M31::ZERO; tree[2 * i].len() + tree[2 * i + 1].len() - 1];
        for (j, a) in tree[2 * i].iter().enumerate() {
            for (k, b) in tree[2 * i + 1].iter().enumerate() {
                d[j + k] = d[j + k].add(a.mul(*b));
            }
        }
        tree[i] = d;
    }

    // D^-1 mod X^479, by the same recurrence as the retained full map.
    let mut inv = vec![M31::ZERO; 479];
    inv[0] = M31::ONE;
    for j in 1..479 {
        let mut sum = M31::ZERO;
        for k in 1..=core::cmp::min(j, 271) {
            sum = sum.add(tree[1][k].mul(inv[j - k]));
        }
        inv[j] = sum.neg();
    }
    let mut spectrum = vec![CM31::ZERO; 1024];
    for i in 0..479 {
        spectrum[i] = CM31::from_m31(inv[i]);
    }
    fft1024(&mut spectrum, &roots);

    println!("// SHA256 input pin: r17_fast_g.rs = 26ea54dfeed2beb53990ab133545c9b6ae0e04c8468664d153cb8739a54c3ec6");
    println!("static PREFIX_INVERSE_SPECTRUM: [CM31;1024] = [");
    for x in spectrum {
        println!("CM31 {{ a: M31({}), b: M31({}) }},", x.a.0, x.b.0);
    }
    println!("];\n");
}
