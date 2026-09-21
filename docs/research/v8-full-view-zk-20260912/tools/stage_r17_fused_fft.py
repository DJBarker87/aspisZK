#!/usr/bin/env python3
"""Fuse canonical CM31 butterflies; preserve the exact fixed transform."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS, one_replace
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
assert not a.output.exists()
shutil.copytree(a.stage, a.output)
root = a.output / EXPERIMENTS
meta = json.loads((a.output / 'r17-sbf-probe.json').read_text())
path = root / 'r17_fast_g.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == meta['fast_g_reuse_only'][path.name]['after_sha256']
s = one_replace(before.decode(), 'pub(super) fn fft(', '''// Products and sums below are ordinary u64 operations. Canonical limbs
// imply each expression is nonnegative and < 2^63, including evaluation order.
// P^2 and 2P^2 vanish modulo P; no challenge inversion or rejection is added.
#[inline(always)]
fn butterfly(u: CM31, v: CM31, w: CM31) -> (CM31, CM31) {
    const P2: u64 = 2147483647u64 * 2147483647u64;
    let a = v.a.0 as u64 * w.a.0 as u64;
    let b = v.b.0 as u64 * w.b.0 as u64;
    let c = v.a.0 as u64 * w.b.0 as u64;
    let d = v.b.0 as u64 * w.a.0 as u64;
    (CM31::new(M31::reduce_u64(u.a.0 as u64 + a + P2 - b),
               M31::reduce_u64(u.b.0 as u64 + c + d)),
     CM31::new(M31::reduce_u64(u.a.0 as u64 + P2 - a + b),
               M31::reduce_u64(u.b.0 as u64 + 2*P2 - c - d)))
}

pub(super) fn fft(''', 'fused arithmetic primitive')
s = one_replace(s, '''                let v = a[start+k+len/2].mul(ROOTS[index]);
                a[start+k] = u.add(v);
                a[start+k+len/2] = u.sub(v);''', '''                let v = a[start+k+len/2];
                // This branch depends only on the public transform index.
                let (plus, minus) = if index == 0 { (u.add(v), u.sub(v)) }
                    else { butterfly(u, v, ROOTS[index]) };
                a[start+k] = plus;
                a[start+k+len/2] = minus;''', 'same butterfly outputs')
s = one_replace(s, 'for x in a { *x = x.mul_m31(M31(1 << 20)); }',
    'for x in a { *x = CM31::new(x.a.mul_pow2(20), x.b.mul_pow2(20)); }', 'same inverse normalization')
s = one_replace(s, 'pub(super) fn check() {', '''pub(super) fn check() {
    let limbs = [0u32, 1, 2, 2147483645, 2147483646];
    // Exhaust 5^6 limb-boundary tuples, independently of the FFT schedule.
    for code in 0..15625usize {
        let mut n = code;
        let mut z = [0u32;6];
        for x in &mut z { *x = limbs[n%5]; n/=5; }
        let u=CM31::new(M31(z[0]),M31(z[1]));
        let v=CM31::new(M31(z[2]),M31(z[3]));
        let w=CM31::new(M31(z[4]),M31(z[5]));
        let product = v.mul(w);
        assert_eq!(butterfly(u,v,w),(u.add(product),u.sub(product)));
        // Checked host arithmetic validates every intermediate evaluation order.
        let p2=2147483647u64*2147483647u64;
        let a=z[2] as u64*z[4] as u64; let b=z[3] as u64*z[5] as u64;
        let c=z[2] as u64*z[5] as u64; let d=z[3] as u64*z[4] as u64;
        let raw = [
            (z[0] as u64).checked_add(a).unwrap().checked_add(p2).unwrap().checked_sub(b).unwrap(),
            (z[1] as u64).checked_add(c).unwrap().checked_add(d).unwrap(),
            (z[0] as u64).checked_add(p2).unwrap().checked_sub(a).unwrap().checked_add(b).unwrap(),
            (z[1] as u64).checked_add(2*p2).unwrap().checked_sub(c).unwrap().checked_sub(d).unwrap()];
        assert!(raw.iter().all(|&x| x < (1u64<<63)));
    }
    for i in 0..2048 {
        let u=CM31::new(M31((i*97+3) as u32),M31(2147483646));
        let v=CM31::new(M31(2147483646),M31((i*31+9) as u32));
        let product=v.mul(ROOTS[i]);
        assert_eq!(butterfly(u,v,ROOTS[i]),(u.add(product),u.sub(product)));
        assert_eq!(CM31::new(u.a.mul_pow2(20),u.b.mul_pow2(20)),u.mul_m31(M31(1<<20)));
    }
    println!("PASS: 15625 butterfly limb-boundary tuples, checked intermediates, all 2048 roots, normalization");''', 'independent fused arithmetic gate')
path.write_text(s)
meta['fused_fft'] = {path.name: {'before_sha256': hashlib.sha256(before).hexdigest(),
                              'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}}
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
