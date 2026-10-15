# Privacy raw-map source inventory — 2026-10-15

Read-only source map for selecting a formal rank route. The formulas below describe the current finite probe and retained rank-gate input. They do not assert universal rank, image inclusion, or privacy.

## Pinned sources

Current source revision: `a17829a776d533d7cd0beeb1f8676dcc793a909c`.

| Source | SHA-256 |
|---|---|
| [`privacy-wide/probe.rs`](privacy-wide/probe.rs) | `54ec15ab6aa9205d3a07d4de56680cd301b6fdfb769dd6281d17b2fb7a13b531` |
| [`lean/D18RawPoint.lean`](lean/D18RawPoint.lean) | `67edf89014f2cc3980eb4e80ffd37875b96042b3252223b5cdee894dfdbf281e` |
| [`lean/DualPad.lean`](lean/DualPad.lean) | `5e8696117c92eb22cee3536ac3594c6eeaed95773f31d076e87078fcc8030c5e` |
| [`lean/DualPadWord.lean`](lean/DualPadWord.lean) | `62372ace48d87078cc459dd887b1b8e4f4897f307e2b37e837bda3849c3de58b` |
| [`lean/DualPadLift.lean`](lean/DualPadLift.lean) | `5f7c11b7cf8c66ce8a5de7b888eaa99de1e61b32d160f4c44dec775c717676ca` |
| Historical `v8-r0-zk-20261009/lean/R0Z/MaskLayout.lean` | `4f0615a66f8abe90b80d1cdff56961356cff13628c85dbd3456f43d9f425b43a` |
| Historical `v8-r0-zk-20261009/lean/R0Z/Z4Maps.lean` | `5e92064e8f9f0f71a5da98a139f1dba8fa3b4463e40831e317f22246e0c63ceb` |
| Historical `v8-r0-zk-20261009/lean/R0Z/Chain.lean` | `c0e5ce0ffd53bee97a8ac9a7c66be4b6d639aac296259416f7799ccaa3e0a4e8` |
| Historical `v8-r0-zk-20261009/lean/R0Z/GoodDensity.lean` | `a4624e603bc89ad8761f6a2df6a50aecc45f7efa0c9d8abac535158beb90322f` |
| Historical `v8-r0-zk-20261009/lean/R0Z/D12.lean` | `272b92f8066f63cf4b57781cfa1f6e586377fadcb1682390acaebda7e4761162` |

The current probe hash also appears as the `probe.rs` input in [`proof-rank-gate-p3/inputs-sources.json`](evidence/privacy-wide/proof-rank-gate-p3/inputs-sources.json). That gate pins one proof and public statement, not a universal family.

## Current observation rows

`probe.rs:2220-2255`, `raw_c_with_transport`, is the current D18 raw-row layout. For each of the 1,024 rows, its base/M31 vector is, in order:

1. one inactive-balance coordinate;
2. three multilinear evaluations (`points(a)` gives `a`, its `b` transform, and its `c` bit-flip transform), each represented by four M31 limbs;
3. one Libra coefficient weight, represented by four M31 limbs;
4. two circle/OOD evaluations, each represented by four M31 limbs;
5. for every query `u`, four M31 scalar evaluations, one per `SlotIndex(0..4)`, at `stored_point(child_index(FibreIndex(u), slot))`.

Thus the base vector has `1 + 3·4 + 4 + 2·4 + 4q = 25+4q` coordinates, with `q=22` giving 113. `c1_raw_ranks` (`:3038-3053`) omits the balance coordinate and the dependent balance row `r=1023`, then takes inactive rows relative to row 1023; the resulting C1 observation width is `24+4q = 112` for the pinned 22-query input. These query-coordinate entries are M31 scalars, not four-limb QM31 values.

The extension-valued raw vector (`:2230-2250`) contains one balance coordinate, the same three multilinear values as single QM31 scalars, one Libra scalar, two OOD scalars, and `4q` query scalars embedded via `QM31::from_m31`. Its width is `7+4q = 95` at `q=22`. `h1_balanced_raw_rank` (`:3057-3070`) forms differences from row 0 over the 810 inactive rows. The H1 padding coordinates themselves are QM31-valued and sampled on `inactive(r)` (`:1950-1967`); balancing is applied by `balance_trace`.

The plain `base_raw`/`ext_raw` path (`:208-282`) predates the explicit D18 transport. The later `raw_c_with_transport` path adds the Libra weight and uses `row_to_coefficient[r]` for Libra/OOD evaluation. `d18_transport` (`:2934-2940`) defines the digit permutation: coefficient digits are read from row digits `[3,4,2,0,1]`, with identity within each base-4 digit. `check_tail_and_transport` (`:2611-2631`) checks invertibility and that each selected C1 eligible row maps to a coefficient whose inverse row remains eligible for that column. This is an executable assertion in the probe, not a general Lean theorem about the full raw map. `D18RawPoint.tensorPoint_eq_booleanRow` and `pointRowMap_eq_row_sum` provide the formal row-coordinate identity for the tensor point map; they do not prove the observation map has full rank.

## Query uniqueness and dependencies

The query generator (`probe.rs:345-363`) produces 22 positions. In its random case it rejects duplicates before sorting; the consecutive, spaced, and paired patterns are also pairwise distinct by construction. The P3 rank gate reads the 22 positions from `Prepared.queries` (`:3139-3144`); the retained run logs 22 specific distinct positions at `transfer13.log:1081`.

Each query contributes exactly four scalar rows, one for each of the four child slots. A repeated query position would duplicate that four-row block. The gate's observed positions contain no repeats. Distinct positions alone do not establish linear independence among the query rows or independence from the other observation families; the probe reports finite matrix ranks instead.

## Mask-column support and the P3 gate

The current probe uses semantic C1 columns `c=0..15`. `eligible(c,r)` is defined at `probe.rs:27-48`: for rows below 912, eligibility is `r % 16 >= 13`; rows 912–1007 and the shifted final 16 rows additionally exclude column-dependent cells. `ACTIVE` and `inactive(r)` (`:16-25`) determine the balanced support. The noise construction (`:1950-1967`) samples an M31 element on eligible C1 cells and a QM31 element for H1 (`c==16`) on inactive rows, then calls `balance_trace`; other lanes in that trace are zero there.

For a C1 column, the raw rank computation uses eligible rows except row 1023 and replaces an inactive row's raw vector by its difference from row 1023 (`:3038-3053`). D18 changes the coefficient index used in evaluations, while the selected source-row support remains the `eligible(c,r)` predicate; the source includes an executable preservation assertion for those selected rows. For H1, the raw balancing map is formed from all inactive rows against row 0 (`:3057-3070`), so the balance relation contributes a forced coordinate. Its observed finite rank is 94 in ambient width 95, with 810 inactive rows, for the single accepted P3 fixture.

The retained gate is [`proof-rank-gate-p3`](evidence/privacy-wide/proof-rank-gate-p3/README.md): it reports C1 ranks 112 for each of 16 columns, H1 rank 94/95, and a separate compensated pure-round image result. These are fixture-specific elimination outputs. The README and receipt give the fixture hashes, actual challenge/query values, D18 source hash, `--release --locked --offline --features private-leaf-salts` command and 4G/6G/0 cap.

## Earlier Z4/Z5/Z8 map lineage

The old branch files are snapshots at these branch revisions; their paths are `docs/research/v8-r0-zk-20261009/z4/probe.rs` unless noted.

| Branch | Probe blob SHA-1 | Relevant layout evolution |
|---|---|---|
| `codex/z4a-structure-20261009` (`z4/z4a/probe.rs`) | `0cafcc46e6e07bcc46b45ed328ccd93833974e57` | Initial structural raw-map and mask-support experiments. |
| `codex/z4c-libra-20261009` | `a0c493da257ee8eafdac36001c57c9f2c0a726d7` | Adds the Libra coefficient column and exact raw C1/H1 map (`base_raw`, `ext_raw`, `raw_c`). |
| `codex/z5-digit-transport-20261010` | `c41b1b9827b96f1d4504aa9009a9e488f4e1b236` | Adds explicit row-to-coefficient digit transport and checks eligibility preservation. |
| `codex/z8-wide-batching-20261013` | `3a1699e6f9e777f9bcaaf1350c604c9d400a528c` | Adds WideExact two-pad/batched experiments while retaining the same raw observation rows. |
| `codex/z8b-decomposition-20261013` | `67542512b0a231b0c77c3abe2582bca0d1c98708` | Adds later decompositions and gate diagnostics over the transported raw map. |

The matching old Lean declarations are in `R0Z.MaskLayout` and `R0Z.Z4Maps`. `MaskLayout.eligible` is a relation on `Fin 29 × Fin 1024`; the legal eligible-noise tape is `F`-valued, and extension mask lanes use four `F` coordinates packed into K. `Z4Maps.roundMask_surjectivity` and `c1_surjectivity` are definitions of propositions (targets), not proved universal surjectivity theorems. `R0Z.Chain.sRem_mem_chain0` proves membership in `Chain0` under its explicit old-model assumptions; it does not prove the current R1 raw-map image inclusion.

The available rank/elimination implementation is computational: `probe.rs`'s `Ech` insertion/elimination and the retained proof-rank gate. The inspected Lean sources contain no determinant/minor/Vandermonde or checked universal rank certificate for this C1/H1 map. `DualPadWord.repair_raw_zero`, `DualPadLift.correction` and `observations_eq` are generic algebraic correction lemmas conditioned on already-supplied preimages/range facts; they do not establish those raw-map facts. The unrelated `R0Z.HonestView.QuotientImage.endpointLinear_surjective` concerns the exact initial encoder with two OOD endpoints, not this observation map.
