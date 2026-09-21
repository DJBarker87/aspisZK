#!/usr/bin/env python3
"""Stage exact in-place dense dual folds and fixed-size query-scale scratch."""
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
path = a.output / 'crates/aspis-core/src/sumcheck.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == '7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead'
s = before.decode()
start = s.index('    fn fold_dense_arity4(')
end = s.index('\n    fn fold_grouped64_binary_deferred_arity4(', start)
body = s[start:end]
body = one_replace(body, '        let mut folded = Vec::with_capacity(chunk_count);\n', '', 'remove per-fold allocation')
body = one_replace(body, '''            folded.push(
                values[offset]''', '''            // Read all four old values before writing. The output index is
            // below every later unread block; no arithmetic order changes.
            let folded = values[offset]''', 'read block before overwrite')
body = one_replace(body, '''                    .half(),
            );''', '''                    .half();
            values[chunk_index] = folded;''', 'write completed scalar')
body = one_replace(body, '        *values = folded;', '        values.truncate(chunk_count);', 'retain owned allocation')
path.write_text(s[:start]+body+s[end:])
meta['inplace_dense_fold'] = {'path': 'crates/aspis-core/src/sumcheck.rs',
    'before_sha256': hashlib.sha256(before).hexdigest(),
    'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
path = root / 'r17_host_relation.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == meta['scalar_fma'][path.name]['after_sha256']
s = one_replace(before.decode(), '''        let scales: Vec<_> = (0..Q)
            .map(|_| {
                let v = power;
                power = power.mul(rho);
                v
            })
            .collect();''', '''        let scales: [K; Q] = core::array::from_fn(|_| {
            let v = power;
            power = power.mul(rho);
            v
        });''', 'small fixed-size query scales')
s = one_replace(s, '    p.t.absorb(label::PROFILE, &bytes(&[inc]));', '''    #[cfg(target_os="solana")] { solana_program::msg!("R17:injected"); solana_program::log::sol_log_compute_units(); }
    p.t.absorb(label::PROFILE, &bytes(&[inc]));''', 'injection marker')
s = one_replace(s, '    let terminal = (0..2).fold(K::ZERO, |s, c| {', '''    #[cfg(target_os="solana")] { solana_program::msg!("R17:tail-folds-end"); solana_program::log::sol_log_compute_units(); }
    let terminal = (0..2).fold(K::ZERO, |s, c| {''', 'tail marker')
s = one_replace(s, '''    // Read-only diagnostic of an accepted public proof.''', '''    #[cfg(target_os="solana")] {
        if reference { solana_program::msg!("R17:reference-terminal-accepted"); }
        else { solana_program::msg!("R17:primary-terminal-accepted"); }
        solana_program::log::sol_log_compute_units();
    }
    // Read-only diagnostic of an accepted public proof.''', 'accepted-path marker')
path.write_text(s)
meta['inplace_fold_relation'] = {path.name: {'before_sha256': hashlib.sha256(before).hexdigest(),
    'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}}
gate = root / 'r17_tensor_check.rs'
s = one_replace(gate.read_text(), 'fn main() {', '''fn main() {
    // Differential control against the retained old dense fold formula.
    for log_len in [2u32,4,6,8,10] {
        for case in 0..20 {
            let mut expected: Vec<K> = (0..1u32<<log_len).map(|j| match case {
                0 => K::ZERO,
                1 => K {c0: CM31::new(M31(P-1),M31(P-1)),c1: CM31::new(M31(P-1),M31(P-1))},
                _ => sample(case*1024+j),
            }).collect();
            let mut actual = WeightAccumulator::empty(log_len);
            actual.add_dense(expected.clone()).unwrap();
            for round in 0..log_len/2 {
                let alpha = match case { 0=>K::ZERO, 1=>K::ONE,
                    2=>K::from_cm31(CM31::from_m31(M31(P-1))), _=>sample(case*13+round) };
                let a2=alpha.square(); let a3=alpha.mul(a2);
                expected=expected.chunks_exact(4).map(|v|
                    v[0].add(a3.mul(v[1])).add(a2.mul(v[2])).add(alpha.mul(v[3])).half().half()).collect();
                actual.fold_deferred_relation_arity4(alpha);
                for (i,&v) in expected.iter().enumerate() { assert_eq!(actual.weight_at(i as u32),v); }
            }
        }
    }
    println!("PASS: 100 dense-fold schedules, every round/coordinate equals old allocating formula");''', 'focused dense fold gate')
gate.write_text(s)
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
