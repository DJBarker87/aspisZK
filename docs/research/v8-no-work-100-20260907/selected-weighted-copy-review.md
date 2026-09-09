# Selected weighted copy rows: deterministic balance bridge

Continuation from `f19673b4fe72cf74ae687a926eeae9d1e5a6a52e` on the existing
research branch. Production, transcript grammar and proof-body maximum are
unchanged. This is a focused deterministic prerequisite, not an accepted
payment theorem or a new probability budget.

## Scope and proved implication

The new leaves port the useful generic algebra from
`NativePaymentCompiledCopyLogUpV1` to the **selected factored two-slot row
expression**, and specialize its whole-table consequence to the current
1024-row active mask. The complete Native leaf and its immediate prerequisite
were absent from both the pinned overlay and the inspected NUC native cache.
Rather than build their unrelated 78/75-link endpoint closure, the new core
uses narrow Mathlib imports and records the algebraic port explicitly.

The kernel-checked statement is:

> All Boolean active copy-row residuals vanish; the total helper sum and
> inactive helper sum vanish; and every slot denominator used at an active
> row is nonzero. Then the active rows' weighted rational balance is zero.

If the row constructor also has zero producer and consumer weights outside
the fixed active mask, the entire row sum is zero. That last static-layout
condition is explicit, not hidden behind an assumption of witness validity.

Both focused leaves passed on the NUC. Their twelve printed axiom audits
contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
This closes the selected-mask weighted-row balance step, not the registered
136-link-to-alias or accepted-payment endpoint.

## Exact algebra and source map

In `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs`, set
`p_s = chi - producer_values[s]` and
`c_s = chi - consumer_values[s]`. The actual source computes

```
(p0*p1) * (H*(c0*c1) + wc0*c1 + wc1*c0)
  - (c0*c1) * (wp0*p1 + wp1*p0).
```

`SelectedWeightedCopyCore.sourceResidual_eq_expanded` connects exactly this
factorization to the generic Native expression. The pole-aware row lemma
then derives

```
H = wp0/p0 + wp1/p1 - wc0/c0 - wc1/c1.
```

This is valid for arbitrary field values and public weights, not only honest
proof inputs. Summing the active rows and using both helper boundaries proves
the global row balance. No root count, decoder, codeword or payment predicate
is assumed or inferred.

### Zero-weight poles are retained

`accumulate_endpoint` adds the compressed value independently of its public
weight. Thus a link with weight zero can still contribute a zero denominator
to the cross-multiplied local check. `NoSlotPole` covers **all four slots** on
each active row. The regression `zero_weight_pole_regression` has all weights
zero and a producer value equal to chi: its source residual is zero even
with helper one, while its rational contribution is zero. This explains why
an active-link-only pole premise cannot justify division in the local step.

Zero-weight links may later be removed from the rational multisets, but not
retroactively from this denominator obligation. No probability is attached
to these poles in the present leaves.

### Literal public data

`SelectedWeightedCopyCore.weightBit/publicWeight` models all five source
weight kinds: one, transfer-only, withdrawal-only, append-left, append-right.
Each weight is zero or one; left/right weights at a public append bit sum to
one. Variant and append index are theorem inputs fixed by caller/public
binding, not values decoded from a witness direction row.

`SelectedWeightedCopyRows` records the source's 64 `ACTIVE_ROW_MASKS`, using
block `row/16` and bit `row%16`, for 1024 Boolean rows. Its 136-link public
weight schedule is:

- Transfer-only indices 3, 4, 12, 20, 21.
- Withdrawal-only index 22.
- Indices 24 through 63: twenty append-left/right pairs.
- All other indices: weight one, including the 24 private-path triples.

The selected tags are `1124073472 + index`; injectivity is proved symbolically.
These data are from the pinned `pair_forest_copy_terminal_constants.rs`, not
the old 183-link atomic registry or 78/75-link native tables. The source array
and generated metadata comparison is separate evidence from the field proof.

The selected Boolean residual is the literal mask scalar (zero or one)
multiplied by `sourceResidual`. Its equality with the generic gated form is
proved. The existing selector-expansion and sparse-MLE leaves are relevant
to connecting the actual off-domain evaluator to this Boolean row lookup;
they are not silently assumed to translate the entire optimized copy kernel.

## Interface completion map

| Interface | Scope/status |
|---|---|
| Actual factored row polynomial equals Native expanded algebra | Kernel checked in the new core |
| Four-slot pole-aware local residual to helper equality | Kernel checked narrow algebraic port |
| Total and inactive helper boundaries to active/whole row balance | Kernel checked in the new core |
| Actual five public weight kinds and selected tag schedule | Source-shaped definitions, kernel-checked binary/injective proofs, exact metadata comparison |
| Selected 1024-row mask and Boolean gate to row balance | Kernel checked in the new dependent leaf |
| 136 endpoint placements and 14 tuple patterns yield these exact rows | Still required; no arbitrary row interface is called a completed source constructor |
| No weights outside the source active mask | Explicit static-layout premise of the whole-row theorem; must be discharged by that constructor |
| Row sum equals active-link tagged/compressed rational multiset balance | Still required for the selected registry, including zero-weight host-slot versus fixed compiled-slot behavior |
| Chi and lambda collision exclusion implies weighted aliases | Existing Native/V7 proof pattern to port after the selected constructor; no new selected collision bound here |
| Accepted repaired semantic/relation execution enforces local rows and both helper boundaries | Separate causal/probability/source theorem; not an `inactiveExact` assumption disguised as acceptance |
| Those aliases plus selected residuals yield one checked payment witness | Existing amount/note/path/output/append endpoints are reusable; complete decoder/compiler/caller composition still required |

In particular, these leaves do **not** derive all 2,176 host copy-alias
residuals from verifier acceptance. For a link of public weight zero the
correct endpoint is `weight*(producer-consumer)=0`, not forced tuple
equality. The remaining registered-link theorem must preserve that distinction.

## Focused evidence and costs

The core was compiled first, followed by the dependent mask wrapper. All
jobs used the isolated task
`/home/dombarker/project-offloads/aspis-covered-family.rfQFkf`, the pinned
Lean 4.32.0 native cache and `run_covered_family_nuc.sh`. The cgroup recorded
MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, and CPU quota 200%; Lean
used `-j1 -M9500`. No dependency or package rebuild ran. Narrow imports kept
actual peak memory below 1.8 million KiB for both leaves.

| Focused target | Exit | Wall | Peak RSS (KiB) | Swaps | Axiom audit |
|---|---:|---:|---:|---:|---|
| Core v1 | 0 | 1.38 s | 1,761,188 | 0 | 7 standard-only |
| Rows v1, retained diagnostic | 1 | 0.83 s | 1,723,944 | 0 | Failed instance; not success evidence |
| Rows v2 | 0 | 0.89 s | 1,734,220 | 0 | 5 standard-only |

Rows v1 failed only because typeclass search did not unfold `rowActive` to
find its Boolean-equality decision procedure. V2 explicitly unfolds that
definition before `infer_instance`; it changes no mathematical predicate,
mask, weight, hypothesis, or resource limit. The failed source is retained
as `selected-weighted-copy-rows-nuc-v1-source.txt`, with SHA
`86ee33175d8411465b82f69229681ed54278ce2a52403d9908ec695c58e4fd00`.
Its downstream `sorryAx` output belongs to the failed elaboration and is not
counted among the final results.

Retained evidence is under `experiments/`: all three
`selected-weighted-copy-{core,rows}-nuc-v*.log` files, their per-run
`-manifest.json` files, the failed source snapshot, and both green oleans.
Both successful runs report unchanged overlay provenance before and after
checking. Native package artifacts remain a pinned-revision cache boundary,
not a claimed replay of their compilation.

| Artifact | SHA-256 |
|---|---|
| Core source | `b4621e1dd2dcb29cf933957b7142d8d726084b0f3eafb1fe75106889c1b41abd` |
| Core olean | `b7f771868a677fa0a6b2387a5d7fc950d25aeb8409d136c80cbac6124fe1ab46` |
| Rows source | `072c0ac4e46b298b386a8400ea5f8f9a308ea3728448b3cad648af8fb9fb18a3` |
| Rows olean | `890c1d6ea2e2722411ea86b63797ef910c4b414b8fcf344fdc125ec3ad3cd635` |
| Pinned Native algebra source | `86b10589ca637514f0eb772a0bb29e9da28304c50f7aa1627bccf2ddbed1993f` |
| Pinned selected copy evaluator | `50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5` |
| Pinned generated selected copy constants | `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50` |

A read-only metadata comparison additionally checked all 64 mask integers,
all 136 tags, and every link's weight kind and level against `git show` at
the source pin above. It found exactly 214 active rows, the five transfer
indices and one withdrawal index listed earlier, and the twenty append
pairs. This small static comparison is not finite-field enumeration, a
compiler translation, an endpoint-placement proof, or a probability test.

The actual focused commands (fresh tags are required for a justified rerun)
were:

```sh
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-covered-family.rfQFkf/run_covered_family_nuc.sh /home/dombarker/project-offloads/aspis-covered-family.rfQFkf SelectedWeightedCopyCore selected-weighted-copy-core-nuc-v1'
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-covered-family.rfQFkf/run_covered_family_nuc.sh /home/dombarker/project-offloads/aspis-covered-family.rfQFkf SelectedWeightedCopyRows selected-weighted-copy-rows-nuc-v2'
```

No laptop compile, source Rust rebuild, field enumeration, proof generation,
SBF build or CU benchmark is part of this task. These are proof/model files
only: zero verifier operations and zero proof bytes change. The 40,282-byte
maximum, full-view privacy, resource-bounded FS and matched complete-
transaction CU obligations are unchanged.

The next source-facing step is the selected endpoint-placement/pattern
constructor and its sum-to-active-link identity. It makes the proved row
balance usable by the family-wise copy argument without importing an old
registry's collision inventory.
