# Reduction stage

LPf_K004: actual core reduce_u64 contract, every u64, no precondition;
exact two natural folds plus conditional subtraction and canonical result.
LPf_K005 is a compilation failure (missing Kani stubbing flag), not evidence.
K006 (verified reduction stub) and K007 (inline reduction) timed out at90s
on the exact M31 multiplication contract; neither may be used as verified.
No unchanged timeout rerun or larger cap. Q and byte contracts remain pending.

LPf_L001 privately rebuilt unchanged LPe_MersenneReduction. LPf_L002 rejected:
over-broad inherited import closure missing PAln_RowBounds. Replaced with direct
FIo_ReduceBounds/FIo_NativeFuns imports. L003 rejected (UScalar size coercion);
its error-recovery sorryAx report is excluded. L004 passes all three new
LPf_ReductionWord theorems with standard-only axioms. native_reduce proves
actual extracted canonical.reduce succeeds and has the exact residue for EVERY
U64, including casts/wrapping subtraction; no output premise is assumed.
This closes the LPe source word-to-natural reduction row, not Q multiplication,
Dot composition, either opaque verifier leaf or any actual-top premise.

Metadata G001–003 failed before Kani because the new scratch tree lacked frozen
path dependencies. All missing source directories were restored by git archive
from the exact frozen revision. K008 then found another frozen tree-reference
include; it too was restored from that revision. No manifest/lock was modified.
These setup failures are retained openly; Kani was not launched for G001–003.
Full source snapshots/hash/resource/axiom records are in the per-attempt receipts;
exact scratch changes are retained as per-run patches. No release replay claimed.
