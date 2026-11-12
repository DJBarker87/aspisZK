#!/usr/bin/env python3
"""X1 stage 2, item A: give every shift amount on the 19 shift rows the type u32 (literal suffix, or a widening /
truncating conversion of a variable amount), in the scratch tree given as argument (never src-frz-a).
Each edit is (file, function, old text, new text, expected count)."""
import sys
from pathlib import Path
T = Path(sys.argv[1]); assert 'src-frz-a' not in str(T)
E = [
 ('crates/aspis-core/src/field.rs', 'QM31::mul / mul_add / square (closure partial)', 'let partial = |x: u64| (x & p).wrapping_add(x >> 31);', 'let partial = |x: u64| (x & p).wrapping_add(x >> 31u32);', 3),
 ('crates/aspis-r1-cost-probe/src/fast_domain.rs', 'fast_domain::fibre_point', 'TABLE_B[index >> 9]', 'TABLE_B[index >> 9u32]', 1),
 ('crates/aspis-r1-cost-probe/src/multiproof.rs', 'multiproof::merged_level', '        let parent = index >> 1;\n        if has_next && next == index ^ 1 {', '        let parent = index >> 1u32;\n        if has_next && next == index ^ 1 {', 1),
 ('crates/aspis-r1-cost-probe/src/one_tx.rs', 'one_tx::base_query (closure fold)', 'let fold = |z: u64| (z & P64) + (z >> 31);', 'let fold = |z: u64| (z & P64) + (z >> 31u32);', 1),
] + [
 ('crates/aspis-r1-cost-probe/src/one_tx.rs', 'one_tx::base_fold', 'acc[b%s] = (acc[b%s] & P64) + (acc[b%s] >> 31);' % (s, s, s), 'acc[b%s] = (acc[b%s] & P64) + (acc[b%s] >> 31u32);' % (s, s, s), 1)
 for s in ('', ' + 1', ' + 2', ' + 3', ' + 4', ' + 5', ' + 6', ' + 7')
] + [
 ('crates/aspis-r1-cost-probe/src/one_tx.rs', 'one_tx::merged_keys', 'keys[j] = (u64::from(index) << 8) | j as u64;', 'keys[j] = (u64::from(index) << 8u32) | j as u64;', 1),
 ('crates/aspis-r1-cost-probe/src/one_tx.rs', 'one_tx::merged_tree (and one_tx.rs:1666, the same expression)', 'let index = (key >> 8) as u32;', 'let index = (key >> 8u32) as u32;', 2),
 ('crates/aspis-r1-cost-probe/src/weights.rs', 'Weights::inactive_tensor', 'if S2_INACTIVE_MASKS[g]&(1<<bit)!=0 {m[bit]=m[bit].add(groups[g]);}', 'if S2_INACTIVE_MASKS[g]&(1<<(bit as u32))!=0 {m[bit]=m[bit].add(groups[g]);}', 1),
 ('crates/aspis-r1-cost-probe/src/sampler.rs', 'sampler::qm31_div_pass', '        let dividend = (remainder << 32) | u64::from(rank[j]);', '        let dividend = (remainder << 32u32) | u64::from(rank[j]);', 1),
 ('crates/aspis-r1-cost-probe/src/transport.rs', 'transport::Variant::final_len', 'pub fn final_len(self) -> usize { 1024 >> (2*self.folds()) }', 'pub fn final_len(self) -> usize { 1024 >> ((2*self.folds()) as u32) }', 1),
 ('crates/aspis-statement/src/state_only_poseidon.rs', 'state_only_poseidon::internal_linear_lazy (closure)', 'full_sum[limb] + (u64::from(limbs[limb]) << SHIFTS[lane - 1])', 'full_sum[limb] + (u64::from(limbs[limb]) << u32::from(SHIFTS[lane - 1]))', 1),
 ('crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', 'validate_transition', 'let expected = if level < carry || ((index >> level) & 1) == 0 {', 'let expected = if level < carry || ((index >> (level as u32)) & 1) == 0 {', 1),
 ('crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', 'append_level_packed_selector_tensor', '    let prepared_high = PreparedQm31Multiplier::new(high);\n    if ((next_pair_index >> level) & 1) == 0 {', '    let prepared_high = PreparedQm31Multiplier::new(high);\n    if ((next_pair_index >> (level as u32)) & 1) == 0 {', 1),
 ('crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', 'add_value_lanes', '.add(reconstruct_10(&openings.succ_z).mul_m31(M31(1 << 10)))', '.add(reconstruct_10(&openings.succ_z).mul_m31(M31(1 << 10u32)))', 1),
 ('crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', 'add_value_lanes', '.add(reconstruct_10(&openings.xor12_z).mul_m31(M31(1 << 20)));', '.add(reconstruct_10(&openings.xor12_z).mul_m31(M31(1 << 20u32)));', 1),
 ('crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs', 'Selectors::row', 'self.high[row >> 4].mul(self.low[row & 15])', 'self.high[row >> 4u32].mul(self.low[row & 15])', 1),
 ('crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs', 'accumulate_endpoint_selector_tensor_basis', '    let high = selectors.high[row >> 4];', '    let high = selectors.high[row >> 4u32];', 1),
 ('crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs', 'link_weight', '3 => M31(1 - ((append_index >> link.weight_level) & 1) as u32),', '3 => M31(1 - ((append_index >> u32::from(link.weight_level)) & 1) as u32),', 1),
 ('crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs', 'link_weight', '4 => M31(((append_index >> link.weight_level) & 1) as u32),', '4 => M31(((append_index >> u32::from(link.weight_level)) & 1) as u32),', 1),
]
for f, fn, old, new, n in E:
    p = T / f; t = p.read_text(); c = t.count(old)
    assert c == n, (f, fn, c, n)
    p.write_text(t.replace(old, new)); print('ok', f, fn, n)
