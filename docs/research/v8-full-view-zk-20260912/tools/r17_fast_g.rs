//! Exact power-sum map via a fixed denominator tree and CM31 convolution.
//! Research only: finite gates are not a universal source-refinement proof.
use super::super::corelib::field::{CM31, M31, QM31 as K};
include!("r17_fast_g_tables.rs");

pub(super) fn fft(a: &mut [CM31], inverse: bool) {
    let n = a.len();
    assert_eq!(n, 2048);
    let mut j = 0;
    for i in 1..n {
        let mut bit = n >> 1;
        while j & bit != 0 { j ^= bit; bit >>= 1; }
        j ^= bit;
        if i < j { a.swap(i, j); }
    }
    let mut len = 2;
    while len <= n {
        let step = n / len;
        for start in (0..n).step_by(len) {
            for k in 0..len/2 {
                let index = if inverse { (n - k * step) & (n - 1) } else { k * step };
                let u = a[start+k];
                let v = a[start+k+len/2].mul(ROOTS[index]);
                a[start+k] = u.add(v);
                a[start+k+len/2] = u.sub(v);
            }
        }
        len *= 2;
    }
    if inverse {
        for x in a { *x = x.mul_m31(M31(1 << 20)); }
    }
}

fn numerator(coins: &[K; 271]) -> Vec<K> {
    let mut current = coins.to_vec();
    let mut next = vec![K::ZERO; 271];
    let mut size = 2;
    while size <= 512 {
        next.fill(K::ZERO);
        for start in (0..271).step_by(size) {
            let mid = core::cmp::min(start + size/2, 271);
            let end = core::cmp::min(start + size, 271);
            if mid == end {
                next[start..end].copy_from_slice(&current[start..end]);
                continue;
            }
            let node = 512 / size + start / size;
            // N_left * D_right + N_right * D_left. Denominators are M31.
            for (from, to, other) in [(start, mid, node*2+1), (mid, end, node*2)] {
                let offset = DEN_OFFSETS[other];
                let count = DEN_LENGTHS[other];
                for i in from..to {
                    for k in 0..count {
                        let at = start + i - from + k;
                        next[at] = next[at].add(current[i].mul_m31(DENOMINATORS[offset+k]));
                    }
                }
            }
        }
        core::mem::swap(&mut current, &mut next);
        size *= 2;
    }
    current
}

pub(super) fn apply(coins: &[K; 271], out: &mut [K; 1024]) {
    let num = numerator(coins);
    // One complex workspace is reused for both extension components. No
    // resampling, challenge inversion or data-dependent polynomial degrees.
    let mut work = vec![CM31::ZERO; 2048];
    for component in 0..2 {
        work.fill(CM31::ZERO);
        for i in 0..271 { work[i] = if component == 0 { num[i].c0 } else { num[i].c1 }; }
        fft(&mut work, false);
        for i in 0..2048 { work[i] = work[i].mul(INVERSE_SPECTRUM[i]); }
        fft(&mut work, true);
        for j in 0..1024 {
            if component == 0 { out[j].c0 = work[j]; } else { out[j].c1 = work[j]; }
        }
    }
}

#[cfg(not(performance_sbf))]
pub(super) fn check() {
    assert_eq!(ROOTS[0], CM31::ONE);
    assert_eq!(ROOTS[1].pow(2048), CM31::ONE);
    assert_ne!(ROOTS[1].pow(1024), CM31::ONE);
    let mut power = CM31::ONE;
    for x in ROOTS { assert_eq!(x, power); power = power.mul(ROOTS[1]); }
    let mut signal: Vec<_> = (0..2048).map(|i| CM31::new(M31(i*17), M31(i*31+9))).collect();
    let original = signal.clone();
    fft(&mut signal, false); fft(&mut signal, true);
    assert_eq!(signal, original);
    // Circular convolution has no wrap here: degrees 270+1023 < 2048.
    let mut impulse = vec![CM31::ZERO; 2048];
    impulse[270] = CM31::ONE;
    fft(&mut impulse, false);
    for i in 0..2048 { impulse[i] = impulse[i].mul(INVERSE_SPECTRUM[i]); }
    fft(&mut impulse, true);
    let mut inv = INVERSE_SPECTRUM.to_vec(); fft(&mut inv, true);
    for i in 0..2048 { assert_eq!(impulse[i], if (270..1294).contains(&i) { inv[i-270] } else { CM31::ZERO }); }
    for i in 1024..2048 { assert_eq!(inv[i], CM31::ZERO); }
    // Independently verify D * D^-1 = 1 modulo X^1024.
    for j in 0..1024 {
        let mut sum = CM31::ZERO;
        for k in 0..=core::cmp::min(j, 271) {
            sum = sum.add(inv[j-k].mul_m31(DENOMINATORS[DEN_OFFSETS[1]+k]));
        }
        assert_eq!(sum, if j == 0 { CM31::ONE } else { CM31::ZERO });
    }
    // Arbitrary coin vectors, including maximal canonical limbs and basis edges.
    for case in 0..6 {
        let coins = core::array::from_fn(|i| {
            let n = if case == 0 { 0 } else if case == 1 { 2147483646 }
                else if case == 2 { (i == 0) as u32 }
                else if case == 3 { (i == 270) as u32 } else { (i as u32*97 + case*83) % 2147483647 };
            K { c0: CM31::new(M31(n), M31(n)), c1: CM31::new(M31(n), M31(n)) }
        });
        let mut out = vec![K::ZERO;1024];
        apply(&coins, out.as_mut_slice().try_into().unwrap());
        let mut expected = vec![K::ZERO;1024];
        for i in 0..271 {
            let mut p = M31::ONE;
            for j in 0..1024 { expected[j] = expected[j].add(coins[i].mul_m31(p)); p = p.mul(M31((i+1) as u32)); }
        }
        assert_eq!(out, expected);
    }
    println!("PASS: root order, FFT inverse, convolution edge, denominator inverse, six arbitrary coin maps");
}
