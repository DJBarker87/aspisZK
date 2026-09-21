#!/usr/bin/env python3
"""Fuse scalar multiply-add in original order; reuse weight serialization storage."""
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
assert hashlib.sha256(before).hexdigest() == meta['fused_fft'][path.name]['after_sha256']
s = one_replace(before.decode(), 'fn numerator_into(', '''#[inline(always)]
fn scalar_fma(acc: K, a: K, b: M31) -> K {
    let limb = |x: M31, y: M31| M31::reduce_u64(x.0 as u64 + y.0 as u64 * b.0 as u64);
    K { c0: CM31::new(limb(acc.c0.a,a.c0.a),limb(acc.c0.b,a.c0.b)),
        c1: CM31::new(limb(acc.c1.a,a.c1.a),limb(acc.c1.b,a.c1.b)) }
}

fn numerator_into(''', 'one reduction per fused scalar limb')
s = one_replace(s, 'next[at] = next[at].add(current[i].mul_m31(DENOMINATORS[offset+k]));',
    'next[at] = scalar_fma(next[at], current[i], DENOMINATORS[offset+k]);', 'unchanged merge order')
s = one_replace(s, 'pub(super) fn check() {', '''pub(super) fn check() {
    for x in [0u32,1,2,2147483645,2147483646] {
        for y in [0u32,1,2,2147483645,2147483646] {
            for z in [0u32,1,2,2147483645,2147483646] {
                let a=K { c0: CM31::new(M31(x),M31(y)), c1: CM31::new(M31(y),M31(x)) };
                let acc=K { c0: CM31::new(M31(y),M31(x)), c1: CM31::new(M31(x),M31(y)) };
                assert_eq!(scalar_fma(acc,a,M31(z)),acc.add(a.mul_m31(M31(z))));
                let raw=(x as u64).checked_add((y as u64).checked_mul(z as u64).unwrap()).unwrap();
                assert!(raw < 1u64<<62);
            }
        }
    }
    println!("PASS: 125 scalar FMA boundary triples, distinct limbs and checked intermediate bounds");''', 'independent FMA gate')
path.write_text(s)
changes[path.name] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                      'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
path = root / 'r17_host_relation.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == meta['move_prepared'][path.name]['after_sha256']
s = one_replace(before.decode(), '''    for (channel, v) in ordinary.iter().enumerate() {
        t.absorb(label::PROFILE, &[channel as u8]);
        t.absorb(label::PROFILE, &bytes(v));
    }''', '''    let mut encoded_weights = vec![0u8; 1024*16];
    for (channel, v) in ordinary.iter().enumerate() {
        for (i, value) in v.iter().enumerate() {
            value.write_le_bytes(&mut encoded_weights[i*16..i*16+16]);
        }
        #[cfg(not(target_os="solana"))]
        assert_eq!(encoded_weights, bytes(v), "same serialized transcript weights");
        t.absorb(label::PROFILE, &[channel as u8]);
        t.absorb(label::PROFILE, &encoded_weights);
    }''', 'same complete transcript bytes in reusable buffer')
# Public fixed-stage markers identify the remaining allocation boundary.
s = one_replace(s, '''    let powers = StateOnlySpendQueryPowers::new(p.gamma);''', '''    #[cfg(target_os="solana")] { solana_program::msg!("R17:opened-points"); solana_program::log::sol_log_compute_units(); }
    let powers = StateOnlySpendQueryPowers::new(p.gamma);''', 'opening point marker')
s = one_replace(s, '''    entries.sort_by_key(|e| e.0);''', '''    #[cfg(target_os="solana")] { solana_program::msg!("R17:opened-records"); solana_program::log::sol_log_compute_units(); }
    entries.sort_by_key(|e| e.0);''', 'opening record marker')
s = one_replace(s, '''    // Retain an independently implemented original combined-opening check.''', '''    #[cfg(target_os="solana")] { solana_program::msg!("R17:opened-authenticated"); solana_program::log::sol_log_compute_units(); }
    // Retain an independently implemented original combined-opening check.''', 'opening authentication marker')
path.write_text(s)
changes[path.name] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                      'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
meta['scalar_fma'] = changes
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
