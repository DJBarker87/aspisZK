# Candidate 1: source-prefix and complete caller equivalence

Retained candidate `3ab4faf7f5b488a0c82720717656a0ebf4c46efa` saves
**34,201–34,243 stage-1 CU**, with no settlement saving. Its exact parent is
`f458169f705f25b04e1e29546c621e4665e0f64c`.

The new Lean result is
`CuSavingsGammaCandidate1.source_tx1_equivalence`: complete old/new emitted
`tx1` equality, with the previous local `claim_factor` hypothesis discharged
under an **explicit source-prefix interpretation**. This is a different
source-admission route from a direct full-helper Aeneas extraction. It must
not be described as a successful whole-claim Aeneas replay.

## Source binding and proof

The parent claim begins `let g=powers::<29>(gamma);`. After removing precisely
that first immutable binding, its entire remaining block has exactly the
candidate's 218 Rust tokens. The only table access is copied `g[l]`; the tail
contains no `gamma`, mutable table access, escaping table reference or table
address observation. Both signatures, both complete archived fragments and
frozen production's complete new helper are checked directly against Git.
Unsupported literals/comments/macros are rejected by the narrow extractor.

`extract-gamma-prefix.py` generates the two tail token lists independently from
those source fragments. Lean checks their identity and the prefix descriptor
identity. `CuSavingsGammaSourceBinding.introduce_binder` gives the compositional
binding law for an arbitrary complete-tail interpreter, including errors and
divergence. The parent executes the powers binding followed by that tail; the
candidate receives the table and executes the same tail. No algebraic,
canonical-input, termination, decoder-success or candidate-equivalence law is
assumed for the tail.

`sourceBoundaries` installs these source-directed claim meanings in the
previously checked complete preparation and transaction emissions. There is
one shared tail interpreter, rather than unrelated old/new claim fields.
`source_claim_factor` proves the local equation. The actual preparation's
previously checked success theorem supplies the retained table at its exact
returned gamma, and the existing complete `tx1` composition consumes the local
equation. Parsing, semantic verification, preparation, allocation and observer
failures/divergence retain their original order in that result model.

## Explicit trust boundary

The narrow source-prefix extractor is **trusted syntax-to-model code**. Lean
checks its generated descriptors and their evaluation equation; Lean does not
verify the Python extractor itself or a complete Rust operational semantics.
The source interpretation uses the usual compositional semantics of immutable
local binding and safe shared arrays as values. Its applicability is checked
by the exact-source and restricted table-access audit above. This boundary is
additional to the existing Rust/Charon/Aeneas and primitive/runtime boundaries;
it is not hidden as a claim-equivalence proposition.

Direct whole-claim Aeneas extraction remains unsupported. The original frontend
rejects nested returns. Combining existing nested-return support and the tested
no-branch-join strategy exposes a nested immutable-borrow context mismatch.
A targeted input-reborrow experiment moves that failure to loop-break
composition but does not resolve it. **None of those failed emissions, producer
experiments or partial generated outputs is admitted into this proof.** They
are recorded as diagnostics, not release dependencies. Existing original
preparation/caller emissions and all production Rust remain unchanged.

Consequently, this result closes the source-level claim/caller equation under
the stated prefix interpretation. The earlier tally of **four replacements
closed through their direct source-emission routes is unchanged**. Gamma adds
a fifth source-level equivalence result with this explicitly different trust
boundary; it must not be silently counted as a fifth direct Aeneas closure.
The combined soundness/privacy transfer and compiled-artifact certification
remain separate obligations.

## Verification

Three new focused targets passed, with standard axioms only:

| Target | Receipt | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|
| CuSavingsGammaSourceBinding | gamma-source-binding-b | 2.806 | 2,570,652 | 0 |
| CuSavingsGammaPrefixData | gamma-prefix-data-b | 1.604 | 2,574,892 | 0 |
| CuSavingsGammaCandidate1 | gamma-candidate1-a | 1.604 | 2,575,484 | 0 |

The source-data identity theorems have no axioms. The consuming theorem prints
only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, native-evaluation
or candidate-equivalence axiom. Eleven unchanged preparation/caller targets
and their exact object/source/receipt pins are reused. No package-wide replay
or unchanged runtime rebuild was run.

The launch wrapper observed idle windows, but another session started Lean
jobs during staging. Actual foreign PIDs are retained in the accepted receipts;
these were overlapping focused jobs under the user's later parallel/no-NUC-
limits authorization. No claim of exclusive-host compilation is made.

`GAMMA-CANDIDATE1-FINAL.json` records every selected command, source revision,
features, exit, wall time, RSS, swap, import/cache hashes and `#print axioms`.
The Digest32-style inventory covers `prepared_claim`, `Prepared::new`,
`tx1_prepare` and `tx1`, distinguishing prefix interpretation from complete
Aeneas emissions. The source/receipt audit is:

```
python3 docs/research/100bit-spend-path-20261013/tools/cu-equivalence-20261019/check-gamma-candidate1.py
```

Production source is still frozen at
`39c2971dd16c95858a4cfd2c9ae35da052eacfa9`. Existing codec, ordered hash trace,
checkpoint, injection, strict stack and six-fixture CU evidence is reused from
`../cu-savings-20261019/FINAL-REPORT.md`. No protocol, public-input, checkpoint
or proof encoding changed. No ELF, shared object, LLBC or compiled proof object
is committed. The next largest remaining measured saving is candidate 14
Libra factorization, **33,363–33,427 settlement CU**.
