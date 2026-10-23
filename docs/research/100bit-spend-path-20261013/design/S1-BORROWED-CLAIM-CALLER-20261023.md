# S1 borrowed claim caller and adopted powers

Status: reference composition proved; S1/S6 and the 100-bit target remain OPEN.
No production source change or new artifact adoption.

The adopted verifier source freeze is
25866ec331cc7ce27dd9956609c11d32fa8fa58a. Its `weights::powers` body is byte
identical to the extraction input of the checked early-return proof, including
the final-iteration return. The source re-pin records this equality explicitly
in `evidence/s126-current-caller-20261021/s1-borrowed-caller-powers-repin.json`.
The old candidate packet's historical NOT ADOPTED label is preserved; this is
a new source association, not an alteration of its original provenance.
The concrete multiplication/carrier interpretation and historical extraction
trust boundary are inherited, not reverified by textual comparison.

Before: `first_original_new_claim_and_rank` installed `sourceBoundaries`, whose
powers child is the historical `from_fn` implementation. The subsequent
borrowed-ABI claim theorem had not been connected to that enclosing theorem.

After: `S1BorrowedClaimConcreteCallerV1.first_concrete_borrowed_reference`
installs the original complete Prepared.new control body with
`BorrowedClaimPrepared.boundaries`. Its powers child is `powersPublic`, using
checked early-return powers. Its claim child is the extracted borrowed-ABI
reference, interpreted by the existing concrete dot/field/powers operations.
The existing total source embedding and unchanged-source P6 serializer
interpretation are installed too. No free embedding or serialization callback
is added. One accepted enclosing first execution derives:

- its decoder result and selected public, split, View and semantic result;
- gamma/kappa canonicality and the payload claim meaning;
- exact gamma powers at every cell of the SAME returned scratch array;
- the joint challenge/query/rho trace, with exact row28 serialization;
- the same successful tx1 continuation with release observer None.

No independent decoder, View, semantic, claim/rank, gamma powers, scratch,
canonicality or serialization-success premise is added. The decoder statement
and public carriers are unchanged from the retained enclosing theorem; this
is not a new full ASF8 codec/native SDK theorem. The extra explicit scratch
conclusion comes from the same preparation, not a second power computation.
Source inspection also pins the single `powers::<29>(gamma)` call, its write
into caller-owned g and the exact `prepared_claim(...,g,kappa)` argument.
The claim computes only its seven kappa powers internally.

`claim_eq`, `boundaries_eq` and `originalNew_eq_transport` preserve complete
Result and scratch, including outer failure/divergence and ordinary Rust errors.
They have no successful-child or canonicality premise. The enclosing semantic
conclusion is ACCEPTED-ONLY; it is not totality of first or of arbitrary claim
children. The reused early-return power theorem is TOTAL for all Usize extents
and canonical inputs; canonical gamma/kappa are derived in the accepted run.

Validation used only focused changed targets, Lean4.32.0, atomic local lock,
-j1 -M4400, warm caches, zero swaps:

| Target / accepted attempt | Exit | Wall seconds | Peak RSS bytes |
| --- | ---: | ---: | ---: |
| S1BorrowedClaimPreparedBoundaryV1 / boundary-v2 | 0 | 9.397158208 | 3739254784 |
| S1BorrowedClaimFirstCallerV1 / first-caller-v2 | 0 | 10.395865917 | 3751100416 |
| S1BorrowedClaimConcreteCallerV1 / concrete-caller-v1 | 0 | 32.204118041 | 3582263296 |

Receipts retain exact commands, source revision and SHA256, tools, direct
imports and five standard-only #print axioms reports. The three-target
transitive object hash inventory has 6241 selected objects; no compiled
objects are distributed. Failed initial edits and the superseded green
first-caller-v1 are retained, not release evidence. No unchanged full replay.
Read-only checker: `python3 tools/s1-borrowed-caller-20261023/check.py`.

Remaining: the whole ORIGINAL native prepared_claim execution must be tied to
this reference; a one-step Kani coupling plus the reference loop induction does
not by itself construct that implementation theorem. Actual child totality,
Std/P6 correspondence, allocation/abort/ordered runtime effects and the actual
SDK/account caller remain open. The unrelated child Ops are explicit operations,
not discharged assumptions. S6 additionally needs the full forest codec and
native/owned stage1 connection in session A's handoff. No new trust field or
source decision is silently adopted. Candidate adoption would require the
whole-source equivalence and affected source/artifact re-pins and gates.
