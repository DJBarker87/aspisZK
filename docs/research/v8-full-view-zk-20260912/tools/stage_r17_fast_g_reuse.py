#!/usr/bin/env python3
"""Reuse output/tensor scratch and batch canonical products in G tree merges."""
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
changes = {}
path = root / 'r17_fast_g.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == meta['fast_g'][path.name]
s = before.decode()
start = s.index('fn numerator(')
end = s.index('\npub(super) fn apply(', start)
s = s[:start] + '''// Both numerator buffers are disjoint slices of the already allocated output.
// At return, the numerator occupies out[0..271]. The FFT consumes c0 before
// overwriting c0, then consumes the untouched c1 before overwriting c1.
fn numerator_into(coins: &[K; 271], out: &mut [K; 1024]) {
    let (first, rest) = out.split_at_mut(271);
    let (second, _) = rest.split_at_mut(271);
    let (mut current, mut next) = (first, second);
    current.copy_from_slice(coins);
    let mut swapped = false;
    let mut size = 2;
    while size <= 512 {
        for start in (0..271).step_by(size) {
            let mid = core::cmp::min(start + size/2, 271);
            let end = core::cmp::min(start + size, 271);
            if mid == end {
                next[start..end].copy_from_slice(&current[start..end]);
                continue;
            }
            let node = 512 / size + start / size;
            for j in 0..end-start {
                let mut acc = [M31::ZERO; 4];
                let mut sums = [0u64; 4];
                let mut pending = 0;
                for (from, to, other) in [(start, mid, node*2+1), (mid, end, node*2)] {
                    let offset = DEN_OFFSETS[other];
                    let count = DEN_LENGTHS[other];
                    let lo = j.saturating_sub(count-1);
                    let hi = core::cmp::min(j+1, to-from);
                    for i in lo..hi {
                        let a = current[from+i];
                        let b = DENOMINATORS[offset+j-i].0 as u64;
                        sums[0] += a.c0.a.0 as u64 * b;
                        sums[1] += a.c0.b.0 as u64 * b;
                        sums[2] += a.c1.a.0 as u64 * b;
                        sums[3] += a.c1.b.0 as u64 * b;
                        pending += 1;
                        if pending == 4 {
                            // Four canonical M31 products are strictly below 2^64.
                            for k in 0..4 { acc[k] = acc[k].add(M31::reduce_u64(sums[k])); }
                            sums = [0;4]; pending = 0;
                        }
                    }
                }
                if pending != 0 {
                    for k in 0..4 { acc[k] = acc[k].add(M31::reduce_u64(sums[k])); }
                }
                next[start+j] = K { c0: CM31::new(acc[0],acc[1]), c1: CM31::new(acc[2],acc[3]) };
            }
        }
        core::mem::swap(&mut current, &mut next);
        swapped = !swapped;
        size *= 2;
    }
    if swapped { next.copy_from_slice(current); }
}
''' + s[end:]
s = one_replace(s, '    let num = numerator(coins);', '''
    #[cfg(target_os="solana")] { solana_program::msg!("R17:G-tree-start"); solana_program::log::sol_log_compute_units(); }
    numerator_into(coins, out);
    #[cfg(target_os="solana")] { solana_program::msg!("R17:G-tree-end"); solana_program::log::sol_log_compute_units(); }''', 'in-output numerator')
s = one_replace(s, 'if component == 0 { num[i].c0 } else { num[i].c1 }',
    'if component == 0 { out[i].c0 } else { out[i].c1 }', 'consume component before overwrite')
s = one_replace(s, '\n}\n\n#[cfg(not(performance_sbf))]\npub(super) fn check()', '''
    #[cfg(target_os="solana")] { solana_program::msg!("R17:G-fft-end"); solana_program::log::sol_log_compute_units(); }
}

#[cfg(not(performance_sbf))]
pub(super) fn check()''', 'FFT profiling boundary')
# Exhaust every coin basis position with distinct nonzero extension components.
s = one_replace(s, '    println!("PASS: root order, FFT inverse, convolution edge, denominator inverse, six arbitrary coin maps");', '''
    let tag = K { c0: CM31::new(M31(3),M31(5)), c1: CM31::new(M31(7),M31(11)) };
    let mut coins = vec![K::ZERO;271];
    let mut out = vec![tag;1024];
    for i in 0..271 {
        coins[i] = tag;
        apply(coins.as_slice().try_into().unwrap(), out.as_mut_slice().try_into().unwrap());
        let mut power = M31::ONE;
        for j in 0..1024 { assert_eq!(out[j],tag.mul_m31(power)); power=power.mul(M31((i+1) as u32)); }
        coins[i] = K::ZERO;
    }
    println!("PASS: all 271 coin basis positions x 1024 outputs; distinct extension components; reused dirty output");
    println!("PASS: root order, FFT inverse, convolution edge, denominator inverse, six arbitrary coin maps");''', 'exhaustive finite basis gate')
path.write_text(s)
changes[path.name] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                      'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
path = root / 'r17_opening_weights.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == meta['tensor_prefix'][path.name]['after_sha256']
s = one_replace(before.decode(), '''    let g = structured.then(|| super::structured_g::mask_weights(z));
    for j in 0..N {
        if transport().inactive[j] { out[j] = out[j].add(K::ONE); }
        if let Some(g) = &g { out[j] = out[j].add(kappa.mul(g[j])); }
    }''', '''    if structured {
        let mut coins = vec![K::ZERO; super::structured_g::COINS];
        super::r17_mask_workspace::mask_weights_into(z,
            coins.as_mut_slice().try_into().unwrap(),
            scratch.as_mut_slice().try_into().unwrap());
    }
    for j in 0..N {
        if transport().inactive[j] { out[j] = out[j].add(K::ONE); }
        if structured { out[j] = out[j].add(kappa.mul(scratch[j])); }
    }''', 'reuse consumed tensor scratch for G map')
path.write_text(s)
changes[path.name] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                      'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
meta['fast_g_reuse'] = changes
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
