# High-support regular candidates and the checked-payment boundary

Focused proof audit at
`e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
`experiments/SelectedEarlyC1Amounts.lean` is kernel-checked; its five axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`. No Rust,
SBF, arithmetic gate or broad Lean replay ran.

## The decisive distinction

A regular, high-support `Qualified` quotient gives one actual original
message `U_gamma = (atGamma d gamma).original Q`. It does **not** by itself
give the 29 component messages or the semantic C1 table.

`SelectedOriginalInjectivity.regular_qualified_unique` identifies quotients
on the same fixed factor/row/gamma. It does not invert gamma batching into
29 messages. `HigherYRegularBranch.regular_branch_count` constructs a
component curve only under an assumed **excess** incidence inequality and
then contradicts the prime factor's higher Y-degree. It is a bound on this
event, not a witness-producing theorem for a single regular candidate.

Consequently the missing upstream implication cannot be phrased as
“large batched support implies payment validity.” It must first supply an
actual component tuple with its own support, or charge a class where such
a tuple is unavailable. Even one gamma-batch equality admits compensating
changes between components; it is not joint component agreement.

The existing exact routes are:

| Interface | Already available result and limit |
| --- | --- |
| `SelectedLinearCover.exists_selected_classification` / `SelectedQuadraticReduction` | Component-family route and separately retained higher-factor events; not every higher-Y candidate enters a component family. |
| `EarlyC1Family.actual_late_projection_member` | A literal 29-tuple with at least 38,228 **own joint** original-symbol matches projects into the C1-only family. Batched support cannot replace this premise. |
| `EarlyC1Family.member_is_base` | Every member is base-valued when the actual fixed C1 word is base-valued. Uses the member's own support and the V7 encoder projection/overlap proof. |
| `EarlyC1CopyCollision.source_member_covered` | For a member of that pre-lambda family, actual local copy/helper/no-pole conditions imply weighted aliases or the declared sequential lambda/chi collision event. |
| `SelectedCopyAliasQM31.transfer_amount_aliases` | Already derives all seven actual transfer amount cell equalities from the 136-link weighted aliases. Its static certificate must be reused, not rebuilt. |

The C1 family is fixed before lambda/chi from C1 alone. C2 need not be
fixed at that time. A later chosen member/helper is allowed only under
membership in this earlier family. The public transfer variant and append
index retain their independent caller-binding obligation.

## Smallest concrete downstream bridge drafted

`SelectedEarlyC1Amounts.member_amounts_or_copy_collision` now connects the
existing copy endpoint to the existing selected amount endpoint, without
assuming its aliases. It takes:

- a member `p` of the actual fixed `EarlyC1Family.family c1` and a base-valued
  fixed C1 word;
- literal `EarlyC1CopyCollision.CopyConditions p .transfer ...`, retaining
  zero local Boolean copy residuals, total and inactive helper sums, and
  **all four** slot non-poles on active rows, including zero-weight slots;
- the exact non-copy fields of `SelectedAmountEndpoint.CompiledAmountResiduals`:
  90 Boolean checks, the three literal Horner recompositions, all six
  auxiliary zeros and both conservation expressions;
- `tablePositivePack (semanticTable p) publicAsset = some 0` for the same
  recovered table, not a decoder- or witness-success hypothesis.

It concludes that the first sixteen columns of `p` are exactly the embedding
of the constructed base-field `semanticTable p`, and either:

1. all three decoded amounts are strictly positive and below `2^30`, input
   equals recipient plus change, and the output sum fits `u32`; or
2. the actual `(lambda,chi)` lies in the existing fixed-family collision set.

The table is constructed from `memberTable p` by the literal `re.re`
projection. `semanticTable_embeds` derives its exact correspondence using
`member_is_base`; no convenient honest table is supplied. The existing
`transfer_amount_aliases` gives the QM31 equalities at source indices
11..17. Projection preserves those equalities. Only seven small Fin-row
versus Nat-row cell-pair identities are new; no 136-link field reduction or
old 183/78/75 registry is introduced. This supplies the actual
`SelectedAmountEndpoint.AliasResiduals` field before invoking
`strict_decoded_amounts`.

This is a substantive but conditional amount endpoint. The draft does not
claim that acceptance enforces the semantic or copy predicates, does not
derive a high-Y candidate's missing component tuple, and does not claim a
complete payment witness. Removing those distinctions would be circular.

## Remaining checked-validator composition

The owner/note/path/afterstate endpoints are **not wholly open**:

- `SelectedMembershipDecode.same_decoded_note_nullifier_and_anchor` joins
  modeled owner/key/note/nullifier equations with the literal 1+20+3 path,
  canonical direction/index decoding and row907/public-anchor residual.
- `SelectedOutputNotes.both_raw_transfer_output_openings` binds the two
  decoded note openings to the independently supplied commitments.
- `SelectedOutputPair.decoded_outputs_feed_checked_pair` proves the modeled
  occupied two-output construction from actual occupancy/copy constraints.
- `SelectedAppendAfterstate.public_output_pair_afterstate` binds the same
  public output pair to the exact modeled append root/frontier transition,
  retaining independent snapshot and static/dynamic afterstate checks.

What remains is a same-recovered-table derivation of **all** these source
predicate fields from the actual semantic/copy/relation event, followed by
the literal compiler/validator interpretation. The new amount draft closes
one concrete field of that composition, not the rest.

The executable research endpoint is
`experiments/recovered_witness.rs:71`, `extract_checked`. It first compares
the independently supplied runtime context with the public outer-forest
binding, then decodes, calls the actual merged-C1 compiler/validator, and
compares the entire compiled public transition with the requested transition.
The outer-root check matters: production
`pair_forest_trace.rs:316` derives a lane root and temporarily replaces the
root in both public input and context before the lower-level validation.
The caller's outer-root authority cannot be inferred from prover columns.

Production `payment_relation.rs:536` additionally validates the caller's
pool/domain/sequence/root/asset and rejects an already-spent nullifier.
Canonical shape/parser access, actual Poseidon/Rust function interpretation,
authoritative context/snapshot, nullifier freshness, and equality of the
whole compiled transition still need their proper source or external-state
premises. None is supplied by polynomial proximity alone. Successful
extraction means **any** witness passes this real check, not necessarily the
dominant C1 candidate; failure of one candidate is not knowledge failure.

## V7 reuse and provenance

The base descent uses the exact V7 `projectBase`/`projectMessage` conventions
in `AspisFormal/AspisFormal/Pool/V7C1SubfieldRecovery.lean` via the selected
`member_is_base` theorem. Its `semanticTrace_embeds_to_selected` is the
existing 29-tuple analogue of the new direct 26-column view.

`V7RestoredSemanticWitness.accepted_restored_trace_implies_decoded_witness_valid`
is only a conditional older endpoint: it requires coherent extraction,
fixed-oracle semantic transcript/claim interfaces, inactive-helper control,
no relevant family failure and faithful hash interpretation. It is not a
theorem for the selected pair-forest compiler and cannot bypass these gaps.
Read-only comparison of both V7 source files with borrowed pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5` was empty.

| Source-review input | SHA-256 |
| --- | --- |
| New `SelectedEarlyC1Amounts.lean` | `146ad131832ffe3a16ee34f6b3ff5491627d52bb9a22c547bfb3cc3920a05318` |
| `EarlyC1Family.lean` | `5131fa466f65931b8c7a8e783e352903b195d12692e56da67bcdfd3918e1ea3a` |
| `EarlyC1CopyCollision.lean` | `cc6dbc2f023c67ba2c81dc6722674f696a8d3101edb3400cdc437d2de7684062` |
| `SelectedCopyAliasQM31.lean` | `a82ddcae4dffa1c8c5e9c3e6a0b65a9a385f1cce425b5eb2d17dde362594e3cb` |
| `SelectedAmountEndpoint.lean` | `93c11b95f35fe345f2f8a756e909f9bca5f3320b7399799d0eabba93a425a7be` |
| V7 `V7C1SubfieldRecovery.lean` | `49b135edbb05cc5b28b8c8a4bda764664f015a7e63bfbbee75f3ffcc0687a3ce` |
| `recovered_witness.rs` | `56760c46ed56ace2756949efabc09f1a2b8880087c1b4dbb7da394a1cc54132f` |

Owned files: the new draft and this report only. No source mass, ideal-law,
Fiat–Shamir, runtime or complete checked-payment theorem is asserted.

## Focused verification

Attempts v1--v3 failed immediately at missing cached imports: first
`SelectedAmountEndpoint`, then its `SelectedSparseMle` dependency, then the
already-green namespaced arithmetic overlay used by that endpoint. No
theorem body was checked in those attempts. The exact previously audited
source/olean pairs were copied into the isolated overlay; no dependency was
rebuilt or modified. Attempt v4 then exited 0 in 2.97 seconds with peak RSS
6,715,436 KiB and zero swaps under MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0, CPUQuota 200%, Lean 4.32.0 and `-j1 -M9500`. Both 917-entry
provenance checks passed.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SelectedEarlyC1Amounts selected-early-c1-amounts-nuc-v4
```

- Source SHA256:
  `146ad131832ffe3a16ee34f6b3ff5491627d52bb9a22c547bfb3cc3920a05318`.
- Olean SHA256:
  `4ec479af027b9eaf68a938b2feb6d6f8d4b05ceaa9a334a80f41cadcc25085a1`.
- Manifest SHA256:
  `0bf428cbdee09382887cc4076580832a50b9f6160891d9eaecda05b5cd1eccfe`.
- Log SHA256:
  `d58ab54452284fd9f58579af34b868818f982039cd3b1f7dd9acd05ed3afb11c`.

This closes a deterministic same-table amount/copy seam only. It does not
turn a high-support gamma-batched quotient into an own-supported component
tuple, and it is not verifier acceptance or a complete payment witness.
