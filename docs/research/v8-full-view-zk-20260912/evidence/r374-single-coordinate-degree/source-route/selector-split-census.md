# Read-only selector split census

This records source coordinates and call/data flow only. It makes no degree claim.

Frozen provenance is from the R368 saved-copy manifest: campaign revision `07977092976005ff691cf381d3e539d3ac06b595`; frozen root `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`; source revision `6677d5f1310ff7373301fbd79f186278f772e68a`. The frozen root lacks Git metadata. Exact complete-file SHA-256 values:

- `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs`: `7371e743a71357f259a58a20c7169188d5c3adb4010c13b6a792c6c65b8cb4a0`
- `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`: `13b68f6db428268b2504068d79c88262e36d9abd22fb60e345612eff6e2cd90b`
- `crates/aspis-statement/src/state_only_poseidon.rs`: `4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe`

`Selectors::at_point` at copy-terminal lines 161–166 supplies `point[..6]` to `high` and `point[6..]` to `low`. Thus the source split is first six coordinates (indices 0–5) for the 64-entry high selector and last four (indices 6–9) for the 16-entry low selector. `Selectors::expand` at lines 144–158 initializes one weight and, for each supplied coordinate, writes the two children at `2 * index` and `2 * index + 1` using `parent.sub(right)` and `right`. `row` at lines 173–177 combines `high[row >> 4]` and `low[row & 15]`.

`poseidon_selectors` at semantic-terminal lines 211–215 assigns `block = sum_high(selectors, &[0..57])` and `local = selectors.low`. Rust's half-open range means this call sums high entries with indices 0 through 56. The projected evaluator at state-only-Poseidon lines 585–617 reads `local[0]`; sums local indices `[1, 9, 10]`; sums indices `2..=8`; passes the local table to the full and internal pair interpolation helpers; and prepares the block value separately. The composed semantic terminal invokes `Selectors::boxed_at_point(point)` and passes `poseidon_selectors(&selectors)` to `evaluate_state_only_poseidon_oracle_projected` (semantic-terminal lines 1253–1256).

This inventory identifies which original coordinate slice feeds the local and block selector values and where those values are consumed. Any algebraic degree use remains a separate proof obligation.
