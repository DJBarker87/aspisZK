# Same-table positivity pack to decoded transfer amounts

Research pin: `1b8f72d9de123b16eb831754e58518e66a33d3f3`. **The new deterministic endpoint is kernel-checked.** Production, Rust, parameters, verifier grammar and proof body are unchanged. This continuation consumes the [private C1 coefficient-recovery result](private-c1-recovery-review.md), but does not assume recovered coefficients satisfy the payment constraints merely because recovery succeeds.

## New deterministic composition

`SelectedAmountEndpoint.lean` connects the same base-field table to the modeled sparse MLE/positive last pack, through the actual selected amount-copy cells, and finally to the natural amounts read by `recovered_witness::decode`:

```
individual selected range, copy-alias and conservation residuals
 + zero positive last pack evaluated from this table's lifted columns1/3
 + canonical raw source amount cells
 -> 0 < input, recipient, change < 2^30
    input = recipient + change
    recipient + change < 2^32.
```

The table is `t(row,column)=c1[column][row]`. The current and successor amount reads are **column1** at rows1014/1015; the inverse is **column3** at row1014. They are not the decoder's column0 note-amount cells. The source copy chains deriving those equalities are explicit below. The QM31 lists are constructed from this same base-field table rather than supplied independently with a desired equality premise.

The premise is individual residual satisfaction and zero value of the specified modeled pack, **not acceptance by the complete verifier**. The theorem assumes neither decoder success, a valid witness, compiler acceptance, nor equality with an honestly generated trace. It gives the transfer compiler's strict amount requirements, not the complete payment/context/settlement predicate.

## Literal source map and prerequisites

The seven singleton-copy records are entries11–17 of `pair_forest_copy_terminal_constants.rs`, tags1124073483–1124073489. Patterns6/7/8/9 select columns0/10/1/2 respectively; each has only tuple lane0 nonzero, and every offset is zero.

| Source tag | Producer cell | Consumer cell | Transfer weight |
|---:|---|---|---:|
| 1124073483 | (44,0) | (1008,10) | 1 |
| 1124073484 | (460,0) | (1010,10) | 1; transfer-only edge |
| 1124073485 | (508,0) | (1012,10) | 1 |
| 1124073486 | (1008,10) | (1014,0) | 1 |
| 1124073487 | (1010,10) | (1014,1) | 1 |
| 1124073488 | (1012,10) | (1015,1) | 1 |
| 1124073489 | (1014,2) | (1015,0) | 1 |

`pair_trace.rs:1103–1131` constructs these legacy tuples. `pair_forest_trace.rs:411–423` shifts the auxiliary rows by48; the frozen selected constants independently expose the resulting coordinates above. `pair_forest_constraint_residuals.rs:258–287` evaluates each tuple lane as `weight*(producer-consumer)`. Its transfer branch at296–322 sets the recipient edge's weight to one. `AliasResiduals` models those seven16-lane differences; `alias_lane_zero` derives the scalar equation used downstream. Slot/tag identities remain relevant to upstream probabilistic copy matching, but do not alter these individual tuple differences. No withdrawal conclusion follows from the transfer-only weight specialization.

`CompiledAmountResiduals` additionally contains:

- The90 Boolean equations in the compiled `b²-b` orientation, not assumed Boolean field values.
- Three literal ten-bit reverse-Horner reconstructions, scaled by 1, 2^10, 2^20, at rows 1008/1010/1012.
- The **six** source auxiliary zeros at column10 of1009/1011/1013/1020/1022/1016.
- The two compiled conservation equations `t1014,0-t1014,1-t1014,2=0` and `t1015,0-t1015,1=0`.

These are the unweighted individual Boolean-row expressions inside `pair_forest_semantic_terminal.rs:466–518`. Their current/successor/XOR12 bit-cell map uses the existing selected `bitCell` convention. The actual `reconstruct_10` at line 168 reverses coordinates 0..8, starting with coordinate 9 and updating `acc+acc+bit`. This source loop is modeled explicitly and proved symbolically equal to its weighted sum, then the full reconstruction is proved equal to the direct 30-bit sum consumed by the V7 range port. The first conservation polynomial is the **negative** of the earlier host/theorem orientation; `compiled_conservation_residuals` proves the zero-predicate implication algebraically. The six auxiliary zeros are preserved in this predicate even though the sufficient downstream range theorem does not need them. They are not any subset of the old 3,803 host-padding equations.

This is a hand-inspected, pinned field-level source model, not a generated Rust registry translation. The endpoint does not yet derive these individual equations from scalar packed semantic/copy acceptance, nor prove all range-row selector/MLE/point correspondence. It does not remove any acceptance check or change the source predicate to accommodate a fixture.

## Proof dependency map

| New declaration | What it derives |
|---|---|
| `sourceHorner_sum`, `sourceBlock_sum` | The literal reverse-Horner field loop equals the ten-bit weighted sum; no assumed helper-correspondence equation. |
| `compiledReconstruction_eq` | Literal three ten-bit block reconstruction equals the selected direct30-bit sum, using the existing symbolic `split_thirty` lemma. |
| `compiled_value_residuals`, `compiled_conservation_residuals` | The old sufficient `ValueResiduals` and `ConservationResiduals` from the explicit new source-shaped residual record, including the seven actual copy links. |
| `liftedColumn_read` | The actual `List.ofFn` QM31 column read equals the literal base-field lift; no independently supplied table correspondence. |
| `liftBase_product_one` | The nested QM31 lift is injective, so the extension product equation is exactly the base-field equation. |
| `table_pack_iff_residual` | The source-modeled current/successor positive pack on lifted table columns1/3 is zero iff the same table satisfies the product-inverse residual. |
| `decoded_source_links` | Source note amounts460/508 equal the corresponding helper rows1014/1015, via the two copy edges per amount. |
| `strict_decoded_amounts`, `strict_raw_amounts` | Positive canonical decoded amounts,30-bit bounds, natural conservation and safe u32 output addition. Input positivity is derived from the positive outputs and conservation. |

The existing `SelectedSparseMle` supplies the literal sparse suffix/index/fold result and optimized1014→1015 successor; `SelectedSelectorExpansion` and the exact V7/QM31 packing identities supply the Boolean pack interface. `SelectedTransferPositive` and `SelectedPaymentRecovery` reuse `ArithmetizationCore.range_value_sound` and `nat_of_field_eq` after constructing the selected30-bit range view. No old accepted-spend capstone is imported as a V8 acceptance theorem.

The old `SelectedTransferPositive` file's historical comment labels the inverse residual an uninstalled control. This continuation uses it as a mathematical lemma for the now opt-in **research** repair recorded in `positive_transfer.rs`; it does not claim production activation. Allowed masks and the reserved inverse cell remain governed by the earlier checked layout work. There is no new masking change or full-view privacy result here.

## Evidence and reproduction

Focused check: **green**. Run under the root-serialized local build slot with an unused log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_amount_endpoint.sh \
  docs/research/v8-no-work-100-20260907/experiments/selected-amount-endpoint-recheck.log
```

The runner checks every reused research source/olean hash and recursively verifies imported repository source against the pin and read-only main cache. It handles the existing local V7 packing overlay separately from the main `ArithmetizationCore` cache. Lean4.32.0 and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` are reused; no dependencies are rebuilt. The single changed leaf runs with `-M7000` and a7,340,032-KiB aggregate child-process RSS stop, with no simultaneous heavy job. Commands, source/olean hashes, time/RSS/swaps and all axiom audits are in the retained logs.

Retained unsuccessful diagnostics:

| Log | Exit | Wall seconds | Peak RSS bytes | Swaps | Correction |
|---|---:|---:|---:|---:|---|
| `selected-amount-endpoint-v1.log` | 1 | 2.70 | 1,183,825,920 | 0 | Import stopped before theorem checking: Lean chose the local `AspisFormal` namespace overlay and did not fall back to main for two missing modules. |
| `selected-amount-endpoint-v2.log` | 1 | 12.81 | 5,513,150,464 | 0 | A generic sum-successor rewrite selected the left nine-term sum instead of the right ten-term sum. Replaced by the explicit named theorem application at index9. |

The import correction copied only the existing, verified matching `ArithmetizationCore.olean` and `ValueConservation.olean` into the local ignored overlay, after checking pinned source identity. Their SHA-256 values are respectively `6ab5f3738e8018b86409fd1ec394527d1e6eded5816817f11385529e0c579300` and `332f6aca6ab9b69eccb050d31895abf1f51ccfc9c97fa9015ab196bee634eaa1`. The successful main cache was reused; no dependency was rebuilt or modified. The second diagnostic's downstream `sorryAx` entries are failed elaboration evidence, not retained proved results.

Final evidence: `experiments/selected-amount-endpoint-v3.log`, **exit 0, 15.42 seconds wall time, 5,656,395,776-byte peak RSS, zero swaps**. All 11 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. There are no new axioms, retained `sorry`, warnings, or resource-guard stops in this successful check.

| Final artifact | SHA-256 |
|---|---|
| `SelectedAmountEndpoint.lean` | `93c11b95f35fe345f2f8a756e909f9bca5f3320b7399799d0eabba93a425a7be` |
| `SelectedAmountEndpoint.olean` (local ignored artifact) | `e36acc1adc53707fde88d140eab6c6669242afab2504a2af6f04eec32ad69e58` |

The final source was not changed after this check. These are proof-check resources, not payment prover, verifier or witness-extractor timings. The three logs preserve the actual environment correction and the changed local proof step rather than silently overwriting failed attempts.

## What remains

The next proof is the actual acceptance-to-individual semantic/copy constraints for authenticated recovered C1, with exact challenge timing, base-field descent and unsuccessful replay/decoder branches retained. This deterministic endpoint supplies **no error term** and does not change the new private decoder's event or134-bit bound. Source refinement, full payment witness reconstruction and authoritative runtime/settlement context remain separate. No public inputs are manufactured from the prover's claims here.

There are no new proof bytes, verifier operations or public messages. The maximum body remains40,282 bytes. No Rust run, SBF build, full-transaction CU, prover-time, real-extractor-time or ZK measurement is claimed by this continuation.
