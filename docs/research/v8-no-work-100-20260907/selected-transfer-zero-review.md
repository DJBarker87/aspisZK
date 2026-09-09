# Selected transfer residuals versus the checked compiler endpoint

Research pin: `bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee`.
Only new isolated research files are changed. No production/default verifier,
payment validator, deployment, or main-branch change is made.

## Question and exact scope

The preceding amount, pair-decoder, forest-path and note-reconstruction leaves
must not be composed into a theorem asserting that every selected-residual-zero
table passes `recovered_witness::extract_checked` without resolving the amount
predicate. That endpoint recompiles the decoded witness using the **pair-forest
compiler**. Its strict positivity conditions differ from the older generic
payment relation.

The new [experiment](experiments/selected_transfer_zero.rs) tests a stronger
statement than the previously proved all-zero **amount-slice** countermodel:
an entire unmasked selected semantic table, with a genuine unchanged synthetic
input-note/key/nullifier/membership path, and correctly regenerated outputs and
append transition. It does not generate an accepting PCS proof, inspect a
deployed transaction, or establish that no alternative valid witness exists.

## Source predicates, not an assumed universal payment specification

| Source at the pin | Literal role |
|---|---|
| `pair_trace.rs:475–508` | Checks runtime binding, spent nullifier, canonical input and membership bounds; `input.value == 0` is rejected |
| `pair_trace.rs:600–630` | Pair transfer compiler rejects either output amount equal to zero, either at least `2^30`, or incorrect checked conservation |
| `pair_trace.rs:938–952` | Pair trace validator calls that same builder before comparing traces |
| `pair_forest_trace.rs:316–346` | Forest compiler delegates to the pair compiler with its temporary lane-root context, then extends and checks the outer forest path |
| `recovered_witness.rs:70–86` | Explicit outer runtime binding precedes decode/recompile; recompiled transition must equal the supplied transition |
| `payment_relation.rs:525–533,574–622` | The **different generic one-tree** relation checks hidden values in `[0,2^30)`, not strict positivity; path type is also different |
| `pair_forest_semantic_terminal.rs:466–518` | Thirty bits, recomposition, six auxiliary-zero conditions, and two conservation equations; no amount-nonzero equation |
| `pair_forest_semantic_terminal.rs:530–580` | Occupancy inverse binds the second commitment's sentinel limb, not its hidden amount |
| `pair_forest_semantic_terminal.rs:1143–1187,1211–1266` | All selected semantic lanes, public digest/asset checks and Copy lane; only public withdrawal amount is explicitly tested nonzero |
| `pair_forest_constraint_residuals.rs:97–197` | Fifteen literal residual classes, 18,089 entries for transfer, including 3,803 padding entries |

The older [payment relation foundation](../v7-pool-payment-relation-foundation.md)
explicitly specifies hidden values in `[0,2^30)`. Consequently a mismatch with
the selected pair compiler's stricter endpoint is not by itself a contradiction
of that older relation. No permission to relax the selected endpoint, or to
silently replace its forest/pair/runtime/settlement predicates with the older
one-tree predicate, is inferred.

## Construction and checks

Start with `recovered_witness::fixture()` and compile its genuine transfer
(`input=1000`, `recipient=600`, `change=400`). A research-only output writer
mirrors the selected compiler's message layout and calls the **actual public
Poseidon round-trace kernel**; its output hashes are independently compared
with the literal note and node hash functions. It reconstructs:

- recipient sponge blocks 27–29 and change sponge blocks 30–32;
- output pair block 33 and append blocks 34–53;
- the direct 30-bit range/conservation cells in rows 1008–1023;
- output occupancy row 1018, using the actual `two_outputs` sentinel/inverse
  constructor;
- the exact next-root/frontier/index using the actual incremental tree append.

All input/key/nullifier cells through row 431, all forest/path cells 864–1007,
and the complete input occupancy row 1017 are asserted unchanged. Unused cells
stay zero. The writer first reproduces the **complete honestly compiled
baseline object byte-for-field exactly**, including metadata and afterstate;
this checks its layout without assuming correctness of the forbidden cases.

The two fixed forbidden controls are `(recipient,change)=(0,1000)` and
`(1000,0)`. Neither is supplied to the honest compiler to produce its table.
For each independently constructed table the test calls the source residual
evaluator and keeps **every one of its 18,089 constraints**, including all
3,803 zero-padding constraints. No failing class is cleared or omitted.

It separately constructs the actual Copy helper and runs the selected compiled
composition at all 1,024 Boolean points with the exact `(row,row+1,row XOR12)`
opening order and fixed, nondegenerate extension-field challenges. This checks
the six auxiliary zeros not separately counted by the host's range inventory.
These are exact finite evaluations at predeclared probes, not a theorem over
all challenges or a soundness experiment. It checks helper sum zero. There is
no nonce/retry search and no hidden randomness supplied to the decoder.

The decoder sees only the C1 table and returns its reconstructed witness. Its
equality with the synthetic construction is an assertion after decoding, not
the definition of success. The source compiler and `extract_checked` are then
called with the correspondingly bound public fields and transition. The
experiment is local and synthetic; caller/account authentication and actual
transaction provenance are not claimed.

## Execution evidence

**Both zero-output controls pass every literal residual and every probed
compiled Boolean composition row, decode successfully, and fail the selected
compiler endpoint with `Conservation`.** The baseline reconstruction exactly
matches the honest compilation and passes checked extraction. This is a
concrete obstruction to the proposed deterministic implication from these
selected residuals to that stricter checked endpoint—not just a missing proof.

| Execution | Public validation | Host residuals | Compiled composition | Decode | Pair compiler / checked extraction |
|---|---|---|---|---|---|
| Genuine baseline 600/400 | Pass | All 18,089 zero | All 1,024 probed rows zero | Pass | Pass |
| Recipient 0 / change 1000 | Pass | All 18,089 zero | All 1,024 probed rows zero | Pass | `Conservation` / reject |
| Recipient 1000 / change 0 | Pass | All 18,089 zero | All 1,024 probed rows zero | Pass | `Conservation` / reject |

Run on Apple aarch64/macOS with `rustc 1.93.0 (254b59607 2026-01-19)`, all
arithmetic compiled with `-O`, new fixture with overflow checks enabled. The
statement library enables the selected V7 kernel feature closure explicitly.
There was no SBF build, network job, or prover run. This executable result is
not labeled a Lean theorem; its axiom audit is not applicable.

| Stage | Exit | Wall | Peak RSS (bytes) | Swaps |
|---|---:|---:|---:|---:|
| Initial direct core compile, missing `OUT_DIR` | 1 | 1.53 s | 245,366,784 | 0 |
| Pinned optimized table-generator compile | 0 | 0.54 s | 123,420,672 | 0 |
| Exact table generation | 0 | 0.62 s | 10,731,520 | 0 |
| Optimized core library | 0 | 5.13 s | 540,753,920 | 0 |
| Optimized statement library | 0 | 9.71 s | 692,436,992 | 0 |
| Initial fixture compile, private constant/field names | 1 | 0.08 s | 118,767,616 | 0 |
| Corrected fixture-only compile | 0 | 0.46 s | 147,718,144 | 0 |
| Complete three-case test | 0 | 0.48 s | 3,620,864 | 0 |

The first failure identified the core build script's generated include; the
runner now generates it from pinned source. The second was local Rust
visibility/naming, corrected to the source's literal note-domain value
(checked against its public hash) and `CM31.a/b` fields. The successful retry
reused the newly built, hash-pinned libraries; it did not rebuild unchanged
dependencies or use old callback libraries. Every stage had a process-tree
RSS guard at 7 GiB; maximum observed use was below 0.7 GB. Logs:

- [v1 preflight failure](evidence/selected-transfer-zero-v1.log)
- [v2 source-pinned library builds and fixture failure](evidence/selected-transfer-zero-v2.log)
- [v3 successful fixture and output](evidence/selected-transfer-zero-v3.log)

Reproduce from the worktree with a new log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_transfer_zero.sh \
  /tmp/aspis-selected-transfer-zero-replay.log
```

This builds the dependency-free libraries from the pin, not a Cargo workspace.
A focused retry may pass the v2 directory as the second argument; the runner
checks both library hashes before reusing it. Recorded artifacts:

| Artifact | SHA-256 / source identity |
|---|---|
| Fixture | `f3c45e2104dd2e61bc9e6bd749e092c823017f3c5008fc2825d9301a948004b9` |
| Reused coefficient decoder | `56760c46ed56ace2756949efabc09f1a2b8880087c1b4dbb7da394a1cc54132f` |
| Core source tree at pin | Git tree `8828bd0c92bec8c3e879c3b333e39015bd69abad` |
| Statement source tree at pin | Git tree `9e4be1b88a2af4cf3f25fa8a0b5a195e6d2639e8` |
| Core library | `18425b7b28369a4b5f3005cd4b22a1897d870e0fe23aef6122f94e8c99040f2b` |
| Statement library | `bbbb9333a8d05aae1b881e498110e43c55858598740757ff75a4519ab33d04f5` |
| Executable | `aef13207eac06bfa8e611e78483fcb59744d04abc0815fb43bf310772376776b` |

Runtime is this coefficient-table diagnostic, **not proving time, end-to-end
extraction time or metered CU**. Fixed challenge probes are not a statistical
security estimate or exhaustive adversarial strategy search.

## Concrete repair/control, not an installed change

If strict positive hidden outputs remain part of the intended selected payment
predicate, there is a small algebraic repair to cost and prove. At the existing
conservation row 1014, `z[1]` is recipient amount and `succ_z[1]` is change
amount. Reserve C1 cell `(row=1014,column=3)` for a base-field inverse `u` and
add the equation

```
z[1] * succ_z[1] * z[3] - 1 = 0.
```

The source mask inventory classifies that cell as relation-free today. Over a
field the equation forces both factors nonzero: if either is zero the left
side is `-1` for **every** inverse witness. Combined with the already proved
canonical 30-bit amount bounds and exact natural-number conservation, this
also forces positive input. A nonzero product admits `u=(r*c)^-1`.

This is a candidate **design change**, not a proof-only fix and not permission
to apply it to V7/production. Its minimum concrete inventory is:

| Item | Increment / obligation |
|---|---|
| Message space and wire | One existing C1 cell becomes a constrained witness cell; no new column, field claim, query, round or root in this model |
| Body | `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` remains the modeled census |
| Prover arithmetic | One M31 product and one checked nonzero M31 inversion |
| Semantic terminal | Two QM31 products for the cubic expression, one selector multiplication, subtraction and packed addition; the conservation selector already exists |
| Packing | New semantic lane 94 fits the existing 24 four-limb packed lanes (capacity 96); no additional theta Horner step |
| Degree | Cubic local witness expression remains below the current degree-25 local maximum; selected/masked global degree needs source confirmation |
| Masking/padding | Remove this cell from the free inventory, 3,803→3,802; update mask schedule/fingerprint and host padding predicate rather than demanding an honest inverse be zero |
| Copy/layout | Existing recipient/change copy links suffice; the inverse is at the check row, so no new link is proposed |
| Transcript | Updated frozen layout/profile identity must be bound before commitments; no separate inverse scalar is transmitted |
| Privacy | Re-establish full-view hiding for the changed constrained cell and responses; losing one free mask cell is not automatically harmless |
| Performance | No CU measurement. The tiny operation inventory is not matched complete-transaction parity |

The existing `PaymentMaskRead` footprint result is reusable for a different,
deterministic fact: row1014/column3 is outside all decoder reads, so changing
that canonical cell cannot directly change the decoded witness. That does not
prove the modified protocol's hiding or its accepted-residual enforcement.

Alternatively, if the intended payment semantics permit zero-valued notes,
the checked extraction endpoint needs an explicitly specified and justified
pair/forest validator with that range convention. The generic one-tree
validator cannot substitute for it. Neither option is implemented here.

## Checked prerequisite for the uninstalled inverse-cell control

[SelectedTransferPositive.lean](experiments/SelectedTransferPositive.lean) now
proves the proposed repair's precise deterministic effect. It does **not**
infer that the installed selected verifier checks this new residual.

| Theorem / interface | Conclusion and dependency |
|---|---|
| `product_inverse_iff` | Over any field, an inverse witness satisfying `r*c*u-1=0` exists exactly when both factors are nonzero |
| `ProductInverseResidual` | Names the proposed literal source-shaped equation at `(1014,1)`, `(1015,1)`, `(1014,3)` |
| `selected_source_products_nonzero` | Existing selected source-value and conservation copy edges transport nonzeroness from those local factors to the recipient/change decoder source cells |
| `representative_positive` | A nonzero M31 field element has a strictly positive canonical natural representative |
| `selected_strict_amounts` | Existing selected `ValueResiduals`, `ConservationResiduals` and the **new, explicitly assumed residual** imply all three decoded amounts lie in `(0,2^30)`, exact natural-number conservation, and a `u32`-safe output sum |

Input positivity is **derived** from the positive outputs and the reused
natural-number conservation theorem. There is no additional inverse, assumed
positive input, decoder success, honest trace equality, compiler acceptance,
or abstract `validWitness` premise. The range/no-wrap mathematics is consumed
from `SelectedPaymentRecovery`, which already ports V7's
`ArithmetizationCore.range_value_sound` and `nat_of_field_eq` to the selected
direct 30-bit cell convention. Those older leaves were not replayed.

The kernel check ran after publication at HEAD
`4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e`, with dependencies matched to source
pin `bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee`. Main/cache source and olean
provenance checks are in the [runner](experiments/run_selected_transfer_positive.sh)
and [focused log](experiments/selected-transfer-positive-v1.log). Result:
**exit 0, 11.57 s wall, 5,625,069,568 bytes peak RSS, zero swaps**. All six
audited declarations use only `propext`, `Classical.choice`, `Quot.sound`;
no `sorry`, new axioms or package replay. The standard finite-field model and
canonical-representative connection are reused; this is not a newly translated
Rust implementation of the gate.

Source SHA-256:
`00f427ff1d17f2b01a7fbb7f18a4bc68b9814d804a05242f0ac34a5d6a9ff48f`.
Compiled olean SHA-256:
`775b0b9796a0b206c279209742bb6a9fdfceb73428f3fe7f5087702bea19b560`.

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_transfer_positive.sh \
  /tmp/aspis-selected-transfer-positive-replay.log
```

This closes a real prerequisite for the costed control. It does not install
the cell, update masking, supply accepted-residual enforcement, or establish
the complete hash/path/context/settlement witness endpoint.

## Implication for the extraction ledger

The obligation must name the exact endpoint. A claim of the form
`selected residuals all zero -> current extract_checked succeeds` cannot be
assumed merely because amount ranges, conservation and the hash/path bridges
are proved separately. Failure of that specified decoder/validator path must
remain charged or its predicate repaired. It does not establish failure of
every possible witness extractor.

The near-gamma, chord/image and authenticated C1 results are unchanged. This
diagnostic neither adds an error bound nor consumes a probabilistic security
budget. Full acceptance-to-recovery, primitive/Fiat–Shamir coupling, ZK and
complete-transaction CU remain separate obligations.

The next endpoint decision is now concrete: pin whether the selected predicate
requires strictly positive hidden outputs. If yes, implement and verify the
costed inverse-cell gate in an isolated research grammar, including its changed
mask inventory. If not, justify a zero-permitting **pair/forest** checked
validator with authoritative context and settlement, rather than retaining the
stricter compiler as extraction success. Neither choice can be made silently
as a formal-proof convenience.
