# R45: legal G transport and encoded OOD preservation

Base: `0f9c5688fbcc1fa94317a01dce52b63f23fb2315` (R44).
Branch: `research/v8-r45-source-mask-transport-20260929`.

## Result

**46 new Lean theorems compile**, with standard axioms only. R44's
normalized quotient directions now have a source-pinned T163 inverse lift
to balanced G-table corrections, preserving all 271 sparse coins. The
actual finite 512/513 carry/scatter model evaluates as multiplication by
the secant line. Interleaving its lanes and retaining 1,024 coefficients
preserves both OOD zeros, with a proved zero tail rather than an assumed
safe truncation. The quotient's two image-tail constraints also vanish.

This does not yet identify the executable Rust remainder loop with the
chosen interpolation section, compose the raw four-channel values with
the complete source circle evaluator, or establish all source residual
equations and the actual oracle law. **It is not full privacy.**

No production/protocol/verifier path changed. No new Rust or SBF execution.
The selected CU endpoint remains **1,620,236 / 1,621,719**; both actual
1M-cap runs exhaust. This milestone claims no CU saving.

## Distinguish G from H1

G has 1,023 free field coordinates with an inactive-row balancing pivot.
Its active coordinates may change. The active-zero restriction belongs
to H1's padding masks, not to G. The R44 next-step wording “balanced/active
table” must not be interpreted as imposing H1's support condition on G.

`mask_is_legal_free_lift` identifies the correction with the retained
nonpivot-coordinate/balanced-table equivalence. This is algebraic legality,
not a proof that deterministic seed expansion produces an independent
uniform table, and not permission to resample previously observed masks.

## Proof chain

| Leaf | New theorems | Established boundary |
|---|---:|---|
| `T163SourceTable` | 10 | Full pinned order/inverse, fixed pivot, inactive membership, agreement with residual prefix |
| `SourceMaskTransport` | 11 | Exact forward/inverse transport, balance, legal free lift, sparse-coin preservation |
| `SourceNaturalShift` | 6 | Current index schedule equals retained generic carry schedule; gather evaluates as multiplication by x |
| `SourceChordEvaluation` | 8 | Exact two-lane chord evaluation and both secant zeros |
| `SourceEncodedOpening` | 8 | Interleaving, safe 1,024 truncation, transported-mask opening and OOD zeros |
| `SourceMaskBoundary` | 3 | Image tails and the combined normalized legal-G boundary |

The main theorem `SourceMaskBoundary.normalized_legal_G_boundary` holds
over any field with nonzero 2, for every injective 22-root tuple, every
fold challenge, each of the 13 selected directions, and two circle points.
It retains balance, all sparse coins, both encoded OOD values, image tails,
safe chord truncation, the four quotient root evaluations and coefficient
fold zero. The last two remain quotient-evaluator statements, not a claim
that their final Rust source composition has already been formalized.

No OOD distinctness is needed for the zero identities. Division by the
secant at query points and admissibility/denominator conditions are separate.
The theorem does not infer correctness or soundness of the whole verifier
from these equalities.

### Source pins and reused mathematics

`generate_r45_transport.py --check` binds the complete ORDER/INACTIVE
inventory to the retained Rust table and R43's stage pins:
`f3ff6a2dea690ebabfe19243186d96a3c0c4bb64beb2bfd601ae1efccd45bb2d`.
It checks 163 moved entries; the 545-entry identity tail is proved
symbolically. The old R36 constructor/table test is retained, not rerun or
relabelled as a new source execution.

`extract_r45_sparse_shift.py --check` verifies verbatim reuse of 14 generic
theorems from `AspisFormal/V5GoodGateSparseShift.lean`, SHA256
`27e474d523dd443e02027e2c77a6c63c978989ef86a4717d3328af58433b35fa`.
Only imports/namespace/audits are adapted. Those theorems are not counted
as new. The proof that the sparse recurrence multiplies by X is reused,
not rediscovered by expanding a large concrete polynomial.

The source helper's `chord` computes 514 even/odd slots, checks the last
four serialized coefficients, then truncates to 1,024. The new evaluator
bridge follows that ordering. The helper's `eval_weights` uses factors
`[y,x,T2(x),T4(x),...]`; `circleWeight` is the corresponding natural-basis
formula. Complete refinement of that Rust bit/product loop and its field
representation is still a source obligation, not an imported premise.

## Executed evidence

Run `python3 docs/research/v8-full-view-zk-20260912/tools/check_r45_evidence.py`.
It verifies the final 222-object cache's source hashes, the unchanged R44
source pins, both generators, successful logs and retained failures.

- New leaves: **10.94 seconds** combined wall time.
- All selected leaves/prerequisites: **15.78 seconds**.
- Largest target peak RSS: **2,634,336 KiB**; all successful targets exit 0,
  report zero swaps, and audit only `propext`, `Classical.choice`, `Quot.sound`.
- **30 retained theorem audits**, separate from the 46 new declarations.
- Serial NUC scopes: `MemoryHigh=3G`, `MemoryMax=5G`,
  `MemorySwapMax=0`, `TasksMax=128`; cached Lean 4.32.0 workspace.
- Every release target, exact command, base revision, source digest,
  timing/RSS/swap and axiom output is retained under
  `evidence/r45-source-mask-transport/` (28 manifest artifacts).

Failed local predecessors are preserved. An inactive-pivot `decide` tried
to reduce the whole finite set; it was replaced by symbolic membership.
The retained well-founded trailing-ones function could not be reduced by
the schedule certificate; a bounded counter was proved equivalent first.
Other failures were explicit-function inference and parity/division rewrite
plumbing. No failure was addressed by increasing recursion, heartbeat or
memory caps; no unchanged package-wide or SBF suite was repeated.

## First remaining proposition

For each admissible source query tuple and selected degree/slot, prove that
the descending natural-basis remainder loop returns the unique degree-below-22
coefficient vector having the same evaluations as that degree's basis
polynomial on all 22 roots. Then its lifted quotient is exactly
`NormalizedQuotient.quotient`, not merely a numerically matching fixture.
The invariant must retain root evaluations at every subtraction and prove
the leading divisor coefficient is nonzero.

Next compose the four quotient channels with the actual circle evaluator
and all residual equations. Derive the new fixed-query challenge polynomial
and its degree rather than reuse the old 1,105 bound. Preserve the Schur
posterior right-hand side `b - B A^-1 a`.

Further release gates remain: H1's separate support/coverage obligations,
coherent pre-beta quotient extraction, shared-oracle/seed/commitment law,
adaptive semantic observations, visible failure/retry/publication accounting,
full-transcript simulation and supported-budget execution. No new hiding
assumption or independent-challenge assumption is introduced here.
