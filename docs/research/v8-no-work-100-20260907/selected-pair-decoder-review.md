# Selected input-pair and direction decoding

Continuation from `5e26df14ad5fc674d5ea43d02431f1dc9ef682fa`; research-only.
This advances the deterministic recovered-C1 endpoint beyond the amount
proof. It does not change the prover, verifier, accepted grammar or wire.

## The slice and its source handoff

The selected coefficient decoder reads the two input commitments from
**path0's ordered children at row 914**, but it reads occupancy/inverse
from row 1017. The selected occupancy residuals constrain a **different
copy of the second commitment**, in row 1017 columns2..9. Therefore merely
checking those local occupancy equations would not establish that the pair
returned by `recovered_witness::decode` is valid.

[`SelectedPairDecoder.lean`](experiments/SelectedPairDecoder.lean) derives
the missing equality from both actual copy edges:

```
decoder second digest, row914 columns8..15
  = node64 right input after removing the lane15 node tweak
  = occupancy digest, row1017 columns2..9.
```

These are the `PrivatePathRight { level:0 }` and `InputSecondCommitment`
edges, each weight one. The same fixed tweak is present at both links, so
it cancels without a special nonzero-field assumption. The theorem then
constructs the existing V7 `PairLeaf.Valid` fact for **the actual decoded
pair**, rather than assuming it or a successful decoder result.

It additionally derives selected-slot spendability using the actual copied
side bit and `selected*(1-occupied)=0`, and proves successful 0/1 parsing of
all 24 private directions. The latter covers input side0, lane-tree levels
1..20, and the three forest levels21..23; it does not conflate the private
historical lane with the public output lane.

## Exact source map and theorem hypotheses

| Item | Cells / source |
|---|---|
| Input first / second commitments | row914 columns0..7 /8..15, `recovered_witness.rs:decode` |
| Occupancy / inverse | row1017 columns0/1 |
| Occupancy certificate's second digest | row1017 columns2..9, sentinel column9 |
| Occupancy selected side | row1017 column10 |
| Actual decoder side | row913 column0 |
| Pair node's adjusted right child | row64 columns8..15; only last limb adds `-0x41531005` |
| All direction rows | `913+16*(level/4)+4*(level%4)`, for `level<24` |
| Last three direction rows | 997,1001,1005; their ordered children are on the successor rows |

`InputPairResiduals` contains 24 direction Boolean equations, the input
occupancy bit/inverse/empty-digest equations, selected-spend equation,
selected-side copy, and the two eight-limb right-child copy edges. This is
a **sufficient subset**, not the complete selected semantic/copy inventory.
No output occupancy or public variant gate is removed or considered proved
unnecessary. No masking coordinate is required to be zero.

Source references at the pinned revision:

- `pair_forest_hiding.rs:144` constructs each selected path-right edge;
  `pair_forest_trace.rs:449` selects the ordered right child and the node
  input's negative tweak.
- `pair_trace.rs:1135` defines `InputSecondCommitment`, and
  `pair_forest_trace.rs:412` relocates its legacy occupancy target by48.
  `InputSelectedSide` is similarly relocated from the legacy direction row
  to913 and the occupancy target to1017.
- `pair_forest_semantic_terminal.rs:558` lists the actual occupancy lanes;
  the input and output row selectors share packed lanes. The individual
  input equations are not inferred directly from one scalar equality.
- `pair_tree_profile.rs:117` checks canonical limbs, then the exact occupancy
  equations and a final occupied-sentinel guard. The field model below
  starts **after canonicality**; it is not a model that accepts malformed
  raw M31 limbs.

For the source-sized 1024-row table, the new symbolic bounds show every
path row and ordered-child successor remains below1008. The previous
`PaymentMaskRead` footprint theorem covers all decoder reads here; it is
reused by scope, not replayed or treated as full-view privacy.

## Reused V7 algebra, new decoder conclusion

`V7PairLeafOccupancy.lean` is reused directly from committed source
`454e793dce86b9d86afe69d992c610dce76fc211`. Its same leaf definitions apply:
first side occupied by convention; second side occupied iff the committed
sentinel is nonzero, with the inverse and empty-digest equations enforced.
No digest-preimage-resistance or salt-liveness premise is imported.

The new source-shaped `validatePairFields` reproduces the **field-stage**
checks of `PoolV1PairLeafWitnessV1::validate`, including the final defensive
occupied-sentinel test. The old V7 nonzero-sentinel theorem discharges that
last branch. The combined `decodeInputPairFields` also parses the actual
side and applies the selected-slot spend check, which the Rust pipeline
performs after pair validation. Its endpoint returns precisely the decoded
pair and direction under the individual residual hypotheses.

This is not a wrapper theorem taking `Valid` as its endpoint premise:
`residuals_imply_checked_input_decode` assumes the concrete residual set
and constructs both validity and successful return. An intermediate generic
validator lemma consumes the newly derived V7 validity fact.

The final conclusions include the occupied second sentinel's nonzeroness
and the empty case's all-zero second digest and zero inverse. Zero
coordinates and an empty unselected second side remain legal. No check is
skipped because it vanishes on honest fixtures.

## Remaining payment path

This closes the field-level input occupancy/side rejection branches and
the per-direction Boolean parser failures, **given these exact residuals**.
It is not yet universal `recovered_witness::decode` or `extract_checked`
success, and it is not a Rust-to-Lean translated-source refinement.

Still required:

1. Canonical shape/field coefficient recovery coupled to actual root-bound
   adversary access. The existing byte-preserving SHA graph/totalized Gao
   work remains the current access model, not a public-root-only decoder.
2. Acceptance enforcing this individual semantic/copy subset, with the
   pre-lambda/chi C1 boundary respected. Packed scalar acceptance alone is
   not assumed to establish all these equations.
3. Selected-current equality, Poseidon block realization and the complete
   21-step pair/lane plus three-step forest root chain; parsing directions
   does not prove hash membership.
4. Owner/key, salts, note/nullifier hashes, amount/public context and exact
   settlement validation. The amount proof remains unchanged. Its strict
   positivity mismatch with the compiler's admission rules is still open;
   occupancy is not a proof that note amount is positive.

The outer authoritative forest-root/runtime check before temporary lane-root
substitution, spent-nullifier context and exact transition comparison remain
required. No caller context is synthesized from prover data here.

The most direct next deterministic bridge is now the pair/lane/forest
hash-chain realization from the same path-ordered cells: compose the
already proved source-selected child relation with existing Poseidon block
equations, without replacing those equations by an assumed final root.

Body remains **40,282 bytes**, with zero new verifier operations/challenges
or extractor messages. No global error number, full-view ZK claim or new
CU measurement follows from this proof.

## Reproduction and evidence

The guarded runner exports the one missing, pinned V7 occupancy olean into
a research-local cache (not concurrent main), then compiles only the new
leaf. It never starts a dependency/package replay. It uses Lean 4.32.0,
Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`,
`-M7000` and a separate 7 GiB aggregate-RSS stop. The imported V7 source
matches the committed research pin and the read-only current main source;
no concurrent K1 module is imported.

```sh
# Once, only when the pinned local occupancy cache is absent:
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_pair_decoder.sh cache /absolute/NEW-cache.log
# The changed leaf, with the exported cache's exact hash enforced:
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_pair_decoder.sh leaf /absolute/NEW-leaf.log
```

| Focused target | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| [Missing V7 occupancy cache](experiments/selected-pair-cache-v1.log) | 0 | 9.66 s | 5,627,969,536 B | 0 |
| [New leaf v1](experiments/selected-pair-leaf-v1.log), universe mismatch | 1 | 3.34 s | 5,501,337,600 B | 0 |
| [New leaf v2](experiments/selected-pair-leaf-v2.log), over-eager simplification | 1 | 3.12 s | 5,502,877,696 B | 0 |
| [New leaf v3](experiments/selected-pair-leaf-v3.log), comment/omit syntax | 1 | 3.12 s | 5,504,909,312 B | 0 |
| [New leaf v4](experiments/selected-pair-leaf-v4.log), final | **0** | **3.25 s** | **5,648,973,824 B** | **0** |

The old V7 type is universe-zero `Type`; the new generic parameter was
matched to that interface. The checker proof now uses the named negative
branch facts directly instead of allowing `simp` to rewrite the limb-zero
predicate before applying its premise. A misplaced `omit` following a doc
comment was then corrected. No budget was raised, no unchanged failing
target was repeated, and no parallel Lean job ran during these checks.

All ten final theorem audits use only the standard subset of `propext`,
`Classical.choice`, `Quot.sound`; no new axiom, `sorryAx` or incomplete
result remains. One harmless unused `DecidableEq K` section-variable
warning remains in `empty_second_is_exact`; that unused typeclass is not
a constraint-satisfaction assumption. The leaf remains over its explicitly
declared decidable field, and this warning does not trigger another replay.

Final leaf SHA256:
`3f670127e035a4ea7f532decb2127386975d2a39e188761dcc9c3eaad55c249e`;
olean `abb67f4a8ec702e4a605a7048081122e5c9ad4462a7449063761ab6aa715c6f8`.
Imported V7 source SHA256:
`eaf609988c11ce5feceac03a7771a143eaccbad8f1025cee0cf0be89c3b350c1`;
exported olean `a483f5baa7101d3c3a3ca6ceb86b7f40993f3fa4f68bfb20d372c05aa5437e6a`.
Failure logs are retained as preflights, not counted as theorem successes.
