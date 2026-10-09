# S3 selected-source history and ordinary-event status

Date: 2026-09-13

Base: `fbe95d2267b419b3570caf844d42060e5e4ab29d`

## Checked source-history additions

S3 adds a restricted section for `projectRecord`. It does not claim global
injectivity: the projection erases actor and merges cached/programmed origin.
For a forward verifier suffix classified as verifier/fresh or verifier/cached,
`liftVerifier` is its inverse while mixed prehistory is retained literally.

`successful_candidate_has_unprojected_final_history` now extracts from an
actual `SuccessfulAlignedChallenge` a final native V7 state and a full suffix
such that its history is the start history followed by that suffix, every
suffix record is verifier/fresh or verifier/cached, and its length is twice
the consumed-block count. This retains `afterAdvance` before any projection.
It is not an accepted-root output-occurrence or probability theorem.

## Exact open selected-source boundary

`FSV8ExactRootCursor.Configuration` still accepts arbitrary `firstWork`,
`secondWork`, `adversaryFuel`, `n`, and `m`; `rootCursor` uses them directly.
The 1511 allocation result takes `adversaryFuel <= q1`, `n + m <= 108`, and a
source-prefix bound as premises. An arbitrary two-query `firstWork` can issue
a marker-shaped query before the intended alpha marker while satisfying the
numeric budget. Thus generic `Configuration` cannot construct first use.

The required missing primitive is a selected V8 configuration/refinement that
constructs the actual script identity/grammar, its resource facts, literal
pre-alpha prefix bound, and the root/local complete-history cut before
projection. Without it, S2 root labels and S3 local suffixes cannot construct
the full `Alpha0RootLabeledTrace` or fresh-output occurrence family.

## Target and event inclusion remain open

The supplied stopped-prefix and polynomial-root drafts compile only as generic
lemmas. The actual event inclusion is blocked because:

* `SameBodyRelation.Arithmetic.evaluate7` lacks a theorem equating it with
  `Polynomial.ofFn 7 (SameBodyRelation.compact ...)` evaluation; and
* `CausalRemainder`/`ConsumedStrategy` retain caller-supplied strategy data,
  so no selected honest/candidate finite polynomial family exists.

Therefore no source `bad-alpha` inclusion into `alpha0OrdinaryRoutedEvent`,
ordinary probability bound, or global soundness number is claimed. Zero
discrepancy, inaccessible candidate data, cached outputs and restoration stay
separate.

## Validation

The archive manifest passed and its 63 finite/reference Python tests passed.
They are not Lean/source proof. Its pin checker found one stale expected blob
for `FSV8V7WholeScriptAlignment`; the current committed source was inspected,
and no old artifact was substituted.

Focused Lean 4.32 checks used the NUC with `MemoryHigh=7500M`, `MemoryMax=8G`,
and `MemorySwapMax=0`:

| Target | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8S3VerifierHistorySection.lean` | 0 | 2.74 s | 6,562,696 KiB | 0 | `propext` only where needed |
| `FSV8S3AlignedUnprojectedHistory.lean` | 0 | 2.80 s | 6,828,104 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |

The aligned draft needed only explicit `FSBoundedTranscript` aliases and a
list-membership normalization. No theorem premise changed. No retained S3
leaf uses `sorry`, `admit`, custom axioms, or `native_decide`.

No production Rust, proof body, q22 parameter, transcript grammar, acceptance
rule, CU claim, privacy theorem, Fiat--Shamir theorem, extraction theorem, or
global soundness claim changed.
