#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
T=Path(__file__).resolve().parent;R=T.parents[1]
v=R/'crates/aspis-r1-cost-probe/src/verifier.rs';s=v.read_text()
fragments={
 'constructor_gather_vec_step':['flat.extend_from_slice(&values);','line_z_values.push(line_z);'],
 'constructor_zero_check':['values.iter().any(|x|*x==M31::ZERO)'],
 'constructor_prefix_push_step':['prefixes.push(product);'],
 'constructor_inverse_write_step':['let i=index-1;','flat_inverse[i]=suffix_inverse.mul(prefixes[i]);'],
 'constructor_group_push_step':['core::array::from_fn(|j|flat_inverse[5*i+j])'],
 'constructor_zero_resize':['let mut flat_inverse=Vec::with_capacity(flat.len());','flat_inverse.resize(flat.len(),M31::ZERO);'],
 'batched_constructor_write_step':['raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];']}
# index-1 is the owned backward-loop cursor; all writes are frozen source.
owned=R/'tools/s7-kani-20261021/src/geometry_owned.rs'
for root,items in fragments.items():
 for item in items:assert item in s or item in owned.read_text(),(root,item)
r=dict(schema='source-step-cut-binding-v1',source_sha256=hashlib.sha256(v.read_bytes()).hexdigest(),owned_sha256=hashlib.sha256(owned.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256((T/'src/vectors.rs').read_bytes()).hexdigest(),fixed_harness_sha256=hashlib.sha256((T/'src/vectors_fixed.rs').read_bytes()).hexdigest(),fixed_ranges={'gather':list(range(22)),'prefix':list(range(110)),'inverse_maximum_vector_length_110':list(range(110)),'group':list(range(22)),'resize':list(range(111))},fragments=fragments,representation='M31 storage represented by its u32 word; scalar arithmetic results supplied to storage-only step cuts. Vec capacity is available preallocated capacity, allocator failure is not modelled by Kani.',bounds={'queries':22,'flat':110,'accumulator_rows':64},scope='Per-function storage and zero-check cuts; not full for_range equivalence or backend arithmetic.')
(R/'docs/research/100bit-spend-path-20261013/evidence/s7-kani2-20261021/vector-binding.json').write_text(json.dumps(r,indent=2)+'\n')
print('Constructor vector step sources bound')
