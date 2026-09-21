#!/usr/bin/env python3
"""Fresh R17 stage; share multilinear prefixes and retain exact host reference."""
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
def edit(name, transform):
    path = root / name
    before = path.read_bytes()
    path.write_text(transform(before.decode()))
    changes[name] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                     'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

edit('relation_callback.rs', lambda s: one_replace(s, 'mod r17_mask_workspace;',
    'mod r17_mask_workspace;\nmod r17_tensor_prefix;', 'tensor module'))
edit('r17_opening_weights.rs', lambda s: one_replace(s,
    'pub(super) fn original_weights(z: &[K; 10], kappa: K, structured: bool) -> Vec<K> {', '''
pub(super) fn original_weights(z: &[K; 10], kappa: K, structured: bool) -> Vec<K> {
    let scales = [kappa, kappa.square(), kappa.square().mul(kappa)];
    let mut out = vec![K::ZERO; N];
    let mut scratch = vec![K::ZERO; N];
    for (i, p) in v6_statement_points(z).into_iter().enumerate() {
        if !(structured && i == 0) {
            super::r17_tensor_prefix::fill(scales[i], &p,
                scratch.as_mut_slice().try_into().unwrap());
            for j in 0..N { out[j] = out[j].add(scratch[j]); }
        }
    }
    let g = structured.then(|| super::structured_g::mask_weights(z));
    for j in 0..N {
        if transport().inactive[j] { out[j] = out[j].add(K::ONE); }
        if let Some(g) = &g { out[j] = out[j].add(kappa.mul(g[j])); }
    }
    out
}
#[cfg(not(target_os="solana"))]
pub(super) fn original_weights_reference(z: &[K; 10], kappa: K, structured: bool) -> Vec<K> {''', 'prefix weights'))
data = Path(__file__).with_name('r17_tensor_prefix.rs').read_bytes()
(root / 'r17_tensor_prefix.rs').write_bytes(data)
# The core gate imports the actual WeightAccumulator, not a copied formula.
(root / 'r17_tensor_check.rs').write_text('''extern crate aspis_core as corelib;
mod r17_tensor_prefix;
#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_structured_g;
use r17_structured_g as structured_g;
mod r17_mask_workspace;
mod r17_opening_weights;
use corelib::field::{M31, CM31, QM31 as K, P};
use corelib::sumcheck::WeightAccumulator;
fn sample(n: u32) -> K {
    K { c0: CM31::new(M31(n % P), M31((n * 3 + 7) % P)),
        c1: CM31::new(M31((n * 5 + 11) % P), M31((n * 7 + 13) % P)) }
}
fn main() {
    for case in 0..20 {
        let point = core::array::from_fn(|i| match case {
            0 => K::ZERO, 1 => K::ONE,
            2 => K::from_cm31(CM31::from_m31(M31(P-1))),
            _ => sample(case * 101 + i as u32),
        });
        let scale = if case == 3 { K::ZERO } else { sample(case * 29) };
        let mut reference = WeightAccumulator::empty(10);
        reference.add_multilinear(scale, point.to_vec()).unwrap();
        let mut out = vec![sample(999); 1024];
        r17_tensor_prefix::fill(scale, &point, out.as_mut_slice().try_into().unwrap());
        for j in 0..1024 { assert_eq!(out[j], reference.weight_at(j as u32)); }
    }
    println!("PASS: 20 cases x 1024 entries equal actual WeightAccumulator::weight_at");
    for case in 0..6 {
        let point = core::array::from_fn(|i| if case == 0 { K::ZERO }
            else if case == 1 { K::ONE } else { sample(case * 101 + i as u32) });
        for structured in [false, true] {
            assert_eq!(r17_opening_weights::original_weights(&point, sample(case * 29), structured),
                r17_opening_weights::original_weights_reference(&point, sample(case * 29), structured));
        }
    }
    println!("PASS: 6 cases x 2 channels x 1024 complete original-weight entries");
}
''')
manifest = root / 'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text() + '\n[[bin]]\nname="r17-tensor-check"\npath="../r17_tensor_check.rs"\n')
meta['tensor_prefix'] = changes
meta['tensor_prefix_sha256'] = hashlib.sha256(data).hexdigest()
meta['callback_after_sha256'] = changes['relation_callback.rs']['after_sha256']
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
