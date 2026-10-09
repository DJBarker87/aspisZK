# Higher-Y recovery continuation

Research parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
No verifier or protocol change is made in this continuation.

## What is newly established

The selected simple-root adapter proves that two qualifying image-valid
quotients on the same regular factor branch reconstruct the same original
message. Their common OOD value is derived from the actual literal
reconstruction. This permits different post-alpha candidates without moving
their choice backwards in the transcript. It proves uniqueness within a
branch, not existence, coverage or a degree-28 curve across gamma.

For the quadratic route, the following components are kernel-checked:

| Component | New conclusion | Remaining premise/application |
| --- | --- | --- |
| `QuadraticSpecializationKernel` | A quadratic root gives a discriminant square; explicit bounded polynomial kernel of the literal Sylvester map, including injectivity | Transport the bounded monomial family into the actual coefficient matrix |
| `QuadraticSpecializationDeterminant` | Kernel columns after invertible basis change give determinant root multiplicity; multiplicity bounds root count | Applied by the checked basis theorem |
| `QuadraticSpecializationBasis` | Constructs the invertible basis change from an independent family; no caller-supplied matrix inverse | Supply the actual independent coefficient vectors from the bounded Sylvester kernel |
| `QuadraticSpecializationCount` | Nonzero resultant and multiplicity m give at most 4 delta parameters; derivative coefficient bound derived; V7 resultant-degree theorem reused | Supply multiplicity and nonzero resultant for the specialization class |
| `QuadraticTwistObstruction` | Nonsquare twist forces a literal pre-OOD coefficient obstruction vanishing at both points | Derive the polynomial decomposition and nonsquare twist from the selected factor |

The twist file also proves a generic whole-polynomial-specialization-zero
coefficient obstruction. With explicit variable reordering this can charge
H_gamma=0 directly; a separate primitivity theorem is not necessary for that
version of the argument. Its degree charge must remain in the ledger.

Focused reports contain the exact statements, hashes, failures and successful
replays: `simple-root-rigidity-review.md`, `quadratic-specialization-review.md`,
`quadratic-count-review.md`, and `quadratic-twist-obstruction-review.md`.
The census is still open while the dependent Sylvester application is built.

## What is not yet established

The proposed restricted quadratic bound `10*degZ(F)` is not a proved
selected-protocol bound. Besides the kernel/basis connection, it requires
polynomial factor decomposition with additive degree accounting, a nonzero
resultant justified in the selected characteristic, and charged content and
degree-drop cases. The twist branch requires its own pre-OOD obstruction
and the actual sequential sampling law. The general higher-Y class includes
factors of degree at least three and is not covered by a quadratic theorem.

Even a completed quadratic bound would bound a classifier contribution,
not establish the full probability of acceptance without resource-bounded
checked payment extraction. Some higher-Y branches can be extractable;
membership in that class must not be equated with knowledge failure.

The earlier near-gamma and insufficient-own-support results remain scoped
as proved. No historical aggregate numerator or grinding contribution is
reintroduced. Source correspondence, full-view ZK and resource-bounded
Fiat–Shamir are separate unfinished endpoints.

## Engineering scope

The maximum proof body remains 40,282 bytes. No CU, prover latency, or
privacy saving is attributed to these algebraic proofs. The exact F5
control and its limited exhaustive family are recorded in
`quadratic-control-results.md`; they are not QM31 security evidence.

All new compilation uses the pinned cached NUC workspace, now accessed via
Tailscale, with bounded serial V8 jobs. Concurrent V7 work is preserved.

The faster positive-complete implementation at
`9e432896a4e1515efebe940b71fd9b4f9f009189` remains a separate implementation
pin. These generic algebraic results do not certify its positivity residual,
changed mask coordinate, compact descriptor or complete source refinement.
Its measured transfer is useful engineering evidence, not a replacement for
the outstanding matched four-shape CU comparison or the proof obligations.

## Next deciding step

Connect the actual bounded Sylvester kernel to determinant multiplicity,
then to the checked 4-delta counting consumer. This removes the central
linear-algebra premise from the proposed nonconstant-X quadratic bound.
Only after that should the selected factor decomposition and causal event
partition contribute a numerical error term.
