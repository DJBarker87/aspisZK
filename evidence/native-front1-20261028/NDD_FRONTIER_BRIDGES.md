# Frontier bridges

Local scope only. No deployed security theorem or global call-edge closure is claimed. Native contracts retain P6/D188 semantic-transport trust.

| Function | Rows | Status | Domain / evidence / remaining obligation |
|---|---:|---|---|
| `crates/aspis-core/src/field.rs::M31::reduce_u62` | 40 | CLOSED-local | value < 2^62; `NDD_Reduce.reduce_cohort`; NDD_K007/NDD_K008 |
| `crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new` | 34 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/weights.rs::field` | 31 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field.rs::CM31::from_m31` | 29 | CLOSED-local | all u32 inputs; `NDD_Simple.cm31_from`; NDD_K009/NDD_K010 |
| `crates/aspis-core/src/field.rs::qm31_pack_base4` | 29 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field.rs::CM31::square` | 28 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::square` | 28 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits` | 26 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums` | 23 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field.rs::CM31::neg` | 22 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field.rs::QM31::neg` | 22 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::index_at` | 22 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed` | 22 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field.rs::qm31_accumulate_product_channels` | 21 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent` | 20 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches` | 20 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent` | 20 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::value_at` | 20 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field.rs::QM31::is_zero` | 16 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field.rs::qm31_m31_dot` | 16 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-core/src/field.rs::M31::neg` | 14 | CLOSED-local | x < 2147483647; `NDD_Simple.m31_neg`; NDD_K011/NDD_K012 |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::neg` | 14 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor` | 14 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor` | 12 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/weights.rs::high_dot` | 11 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts` | 10 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/weights.rs::double` | 10 | OPEN | Pending assigned member work; no bridge credit. |
| `crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard` | 10 | OPEN | Pending assigned member work; no bridge credit. |
