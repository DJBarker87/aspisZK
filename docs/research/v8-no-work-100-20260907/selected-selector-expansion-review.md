# Selected selector expansion: source-loop refinement

Pinned research revision: `51b78cbf7fadee4ec70328c86add7678a43f21da`. This continuation owns only the new Lean leaf, runner, logs and this report. No Rust, green proof leaf, production default or transcript is changed. The new leaf is kernel-checked, with standard axioms only and the source boundaries below.

## What changes

The selector correspondence left open in `PositivePackBinding` is now derived for a mathematical model of the actual descending array loop. It is not imposed as a premise. The result covers every field point, including zeros and ones, not just the honest Boolean fixtures.

The model follows `pair_forest_copy_terminal.rs:143–177`:

1. Start with weight 0 equal to one, all other weights zero, and `len=1`.
2. For each coordinate in forward order, process parent indices in descending order. Read `parent` once; compute `right=coordinate*parent`; write `parent-right` at `2*index` and `right` at `2*index+1`.
3. Double `len`. The high array consumes coordinates 0–5; the low array consumes coordinates 6–9.
4. Return `high[row>>4] * low[row&15]`.

`sourceStores_eq` proves that two sequential functional-array updates give exactly the model's pair write; `sourcePass_eq` lifts this through the descending source loop. The expansion definition calls that literal store loop. `writePair_below` shows that these writes cannot change a still-unread lower parent. `descendingPass_above` shows that subsequent smaller indices cannot overwrite previously produced higher outputs. Together they justify the complete pass formula

`new[j] = old[j/2] * (if testBit(j,0) then coordinate else 1-coordinate)`.

Induction on the number of coordinates then gives

`expand(z,n)[row] = product(i<n, if testBit(row,n-1-i) then z[i] else 1-z[i])`

for `row < 2^n`. The proof never expands a full 1,024-cell array or concretely unfolds the recurrence. Only the source's tiny index constants and four selected row bounds are reduced.

The selected high/low lookup is connected without an index-map assumption: `row>>4=row/16`, `row&15=row%16`; bit positions of division shift by four, and remainder preserves the bottom four bits. Splitting the ten-factor product into lengths six and four then proves `selected_selector_product`.

## Positive pack connection and V7 reuse

Specialising that product to the source's MSB-first Boolean point gives exactly `PositivePackBinding.rowSelector`. `expanded_last_pack_eq` replaces **all four selector occurrences** in the transfer's last packed semantic expression—targets 44, 508, 460 and 1014—by the proved expansion. The resulting endpoint is

`expandedLastPack(1014,asset,publicAsset,r,c,inverse)=0 ↔ r*c*inverse=1`.

The endpoint reuses the preceding exact-QM31 pack proof and V7's maintained pack algebra/tower conventions. It does not assume old asset residuals are zero; their zero selectors at row1014 are derived by the earlier bit-support theorem. It also does not require the five supplied field values to be honestly generated or base-valued.

The inspected V7 selector-sparsity and source-bridge files prove useful grouping identities **given high and low factors**. They do not themselves prove `Selectors::expand` computes those factors, so they were not cited as having already closed this recurrence. Existing field/tower and packing oleans are reused, not rebuilt.

## Exact remaining boundaries

| Boundary | Result/scope |
|---|---|
| Two source assignments and descending overwrite order | New field-level functional-array proofs; arbitrary initial array and coordinate |
| Expansion → MSB-first tensor product | New generic induction, with explicit in-range index condition |
| Actual high6/low4 split and bitwise row addressing | New finite-index arithmetic/product proof |
| Source-shaped row1014 semantic pack → inverse equation | New composition with the green `PositivePackBinding` theorem |
| Actual Rust memory accesses, canonical limbs, prepared multiplication machine code | Not an Aeneas/Rust translation in this leaf; field operations are the mathematical interpretation |
| `multilinear_evaluate_qm31` → recovered table values at current/successor points | Still a distinct source interface: it calls `constraints_v4.rs:601`'s sparse equality-weight helper, not this selector expansion |
| Accepted masked sumcheck → packed Boolean constraints zero | Still requires causal semantic enforcement and the actual fixed C1 object; last-pack zero is not synonymous with acceptance |
| Payment witness, full-view ZK, Fiat–Shamir and complete-transaction CU | Unchanged independent obligations |

The MLE helper was inspected: it strips a trailing Boolean suffix, encodes that suffix in MSB-first order, and enumerates the remaining prefix. At a fully Boolean point it should produce one `(row,1)` entry. That is a precise next source-shaped lemma, but is not claimed merely because this different selector loop is now modeled. Successor row1014→1015 likewise needs its concrete point/evaluation composition; the existing degree proof does not itself identify table values.

No probability term, positive work contribution, proof-body field or verifier operation is added. The maximum body remains 40,282 bytes. This is a deterministic source-model advance, not a new security subtotal or performance measurement.

## Reproduction/evidence

The successful [selected-selector-expansion-v2.log](experiments/selected-selector-expansion-v2.log) records exit **0**, **12.99 s** wall time, **5,676,564,480 B** peak RSS and **zero swaps**. All eleven axiom audits use only `propext`, `Classical.choice` and `Quot.sound`; there are no errors, warnings, `sorryAx` or new axioms in this successful result. Toolchain: Lean `4.32.0`; mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_selector_expansion.sh \
  /absolute/path/to/a-new-selected-selector-expansion.log
```

The runner pins source and reused olean hashes, obtains the cached Lean environment, and enforces a 7 GiB process-tree RSS stop. Runs require a new log path and the explicitly granted serialized build slot; the shell runner does not itself coordinate other agents. No package/dependency replay or Rust/SBF build was performed. The exact changed-leaf command, environment and transitive source/cache provenance are recorded in the log.

| Artifact | SHA-256 |
|---|---|
| `SelectedSelectorExpansion.lean` | `3f6c969a075d37f46d2a93c844191dc7dbb9c974c5413bfdf0a73c92ea50999a` |
| Successful `SelectedSelectorExpansion.olean` | `358d9a496a1e56d9b508cf9fa726d8f597e8a6db6626fe05cb982c6236e256cb` |
| Reused `PositivePackBinding.lean` | `f2332636ff75ac7b397f9fabd7b6479f1df4c63bd071f14013200badd4edea69` |
| Reused `PositivePackBinding.olean` | `3d5b74e3208f993f5aaaa283a128ac586ff5af5e19fe63bc7017d71c8dbaa912` |

`selected-selector-expansion-v1.log` is preserved as a failed diagnostic: exit 1, 16.29 s, 5,523,095,552 B peak RSS, zero swaps. Failures were local parsing/argument inference and natural-index/let normalisation; the replacement names the parent-index bound and normalises the source's odd division and final product index explicitly. No theorem hypotheses were weakened and no resource cap was raised. `sorryAx` entries in that unsuccessful elaboration are not a completed proof or an accepted axiom audit.
