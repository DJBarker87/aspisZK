# Current goal: candidate 12, transaction-local rho residues

User direction: prove the optimizations with the largest measured CU savings
first. Gamma reuse is paused, not completed. Candidate 6 remains the one closed
replacement under the existing reference source/runtime assumptions.

Descending remaining combined incremental saving (six measured fixtures):

| Candidate | Stage 1 | Settlement | Combined range |
|---|---:|---:|---:|
| 12 rho residues | 42,693–42,746 | 51,250–51,356 | 93,943–94,102 |
| 4 delayed base dots | 28,221–28,252 | 33,880–33,932 | 62,101–62,184 |
| 3 fixed S2 groups | 0 | 40,517–40,520 | 40,517–40,520 |
| 1 gamma reuse | 34,201–34,243 | 0 | 34,201–34,243 |
| 14 Libra factorization | 0 | 33,363–33,427 | 33,363–33,427 |
| 2 profiling | 10,992 | 13,201 | 24,193 |
| 5 canonical dots | 11,273–11,286 | 11,617–11,630 | 22,890–22,916 |
| 10 fixed prefix | 5,620 | 6,744 | 12,364 |
| 7 geometry reuse | 780–791 | 947–957 | 1,727–1,748 |

The combined ranges above sum independent minima/maxima, so are conservative
envelopes, not assertions that both extrema occur in the same fixture.
Source: ../cu-savings-20261019/FINAL-REPORT.md.

Completion requires the exact old/new candidate-12 source bridge, canonical
initialization and sufficient-resource allocation admission, all-row query
invariants and checked counter increment, actual canonical reference field
update, finish/checkpoint and caller composition, all covered success/error/
divergence paths and observations under precisely the existing reference
boundary. No unproved candidate-equivalence premise may remain. Focused Lean
checks and #print axioms, pinned source/tool/cache receipts and a pushed proof
commit are required. Production Rust and the root checkout remain untouched.

The goal is not complete merely because the push/value/finish components pass.
No generic compiler expansion is authorized by this goal.

Latest checked source progress: see RHO-INITIALIZER.md and
RHO-REFERENCE-TRAVERSAL.md. Complete initializer outcome is checked through
actual heap::filled (resource binding remains separate). The complete emitted
old coefficient loop now equals the finite reference updates, including
failures/divergence and executed diagnostics. source_batch consumes that
function and the actual emitted basis result against the checked optimized
arithmetic batch. The optimized source Option reborrow interface, actual
caller invariants and sufficient-resource reservation/effects composition
remain open. Do not count this as another fully closed optimization.

The existing strict decoder canonicality proofs under
lean/extracted-decode-k-canonicality-20261018/ include
AspisR1DecodeKFullParserCanonicalityCMQ.qm31_from_le_bytes_success_canonical.
Inspect and reuse these before attempting new decoder proof/extraction work
for Reader.k/resume canonicality. Avoid another Option frontend experiment;
its exact failures are archived in RHO-COEFFICIENT-SOURCE-DIAGNOSTICS.json.

Canonical source routines are now checked: RHO-CANONICAL-INPUTS.md/json.
CuSavingsRhoReader.k_success derives Canonical plus bytes/at frame from the
actual emitted Reader.k; k_outcome covers all Results. CuSavingsRhoScalarK
source_outcome/source_success derive actual sampled rho canonicality while
retaining the arbitrary common block operation. Reuse these; do not redo
strict parsing or sampler digits. The exact original sampler Types/Funs and
ExtractedQM31SamplerDigits were re-pinned in the CU object root with matching
source receipts, then the scalar_k dependents rechecked. Use stage-focused.py
--source for non-flat source roots instead of introducing duplicate files.

The original Reader unwrap carries inherited core.fmt.Formatter : Type;
the exact original object is pinned and unwrap_debug_unused proves its Debug
argument irrelevant. This is not a new equivalence axiom. Canonical audit
whitelists it only for the actual Reader source and Reader theorem module.

The bounded optimized-MIR attempt also failed its reborrow shape gate:
Option.as_deref_mut remains in the successful raw emission. No speculative
primitive implementation has been imported. Evidence is in
RHO-MIR-REBORROW-DIAGNOSTIC.json; do not repeat this extraction configuration.

## Option source boundary checkpoint (after 34b0e558e)

See RHO-OPTION-LOANS.md/json. Exact generic std as_mut/map and identity
DerefMut body extraction now have checked leaf/writeback theorems in
CuSavingsRhoOptionLoans. These are not a binding of original as_deref_mut.
Do not count them as candidate completion. Generic leaf composition fails
when source nested loan types are instantiated; direct branch normalization
also fails handback translation. Do not keep trying producer flags/variants
without a new structural reason. No template/compatible API may stand in for
that source binding. Original production Rust remains frozen.

Proceed with actual caller invariants independently: derive power update and
next framing from the common accumulate suffix, then source Prepared/resume
canonicality/dataflow. The original nested-borrow lowering and final contexts
still must be solved before full candidate completion.
