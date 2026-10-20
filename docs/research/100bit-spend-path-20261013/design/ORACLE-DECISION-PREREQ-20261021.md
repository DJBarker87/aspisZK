# Oracle decision prerequisites, 2026-10-21

Scope: additive prerequisite modules on branch `codex/cx-oracle-prereq-20261021`,
base `26fc9ca35`. No endpoint port is authorised or performed. Existing Lean
modules, S-cone pins and the concurrent M10 instrumentation are untouched.

## Stage 1: issued queries

`OracleDecisionPrereqSampler` proves the uniform transcript allowance 115,
including malformed-message cases: row 0 costs at most 4, row 26 at most 4,
row 31 at most 17, and the other 30 rows at most 3.

`OracleDecisionPrereqPaths` constructs a terminal program that executes all
independent openings, compares their roots, and issues an explicit list of
additional frame/checksum reads. Its terminal count is exactly
`frames.length + sum (depth + 1)`; no acceptance, collision or distinctness
premise enters that count. The last node hash already computes the Merkle
root; comparing the supplied root issues no additional call.

The full verifier's closed allowance is

`B_V(q, d, f) = 115 + 3*q*(d+1) + f`.

For 22 C1/C2/folded queries at binary depth 18 and the study's six
checkpoint/resume reads, `B_V = 1375 > 1161` (increase 214). Terminal calls
are exactly 1260, including 66 leaf hashes, 1188 parent hashes and six frame
reads. With no checkpoint/resume reads the allowance is 1369. The explicit
frame inputs are parameters, not a claim to have implemented the frozen
checkpoint writer/parser. Roots are not double counted.

The smaller 1161 allowance requires shared multiproof execution and its
source/profile correspondence. Neither exists in the feasibility primitives;
independent path recomputation does not establish it. The new theorem bounds
actual issued calls, and hence distinct first reads of the original
experiment by `Q + B_V`, when the prover issues at most Q calls.

## Stage 2: decoder starts

The existing decoder counts recognised fresh *chain starts*, including
ordinary absorb addresses, not only canonical initialisation frames.
`BinInitialQueryAccounting.InitialisationCharging` explicitly labels
initialisation-only charging as an additional restriction which the endpoint
does not assume. The selected message codec enforces only a size bound.
Merkle leaves and nodes start with 16 and 18, whereas initial frames start
with 85; this proves they are not canonical initial frames. It is insufficient
to prove decoder rejection: the absorb parser inspects positions 32 and 33,
which contain unconstrained leaf/child bytes. No universal zero-start claim
is made from this first-byte separation.

`OracleDecisionPrereqStarts` reuses `BinHonestQueryBudget.rows_bound` and
proves exact compiler start preservation for arbitrary effectful decisions.
It gives `Q + 34 + N` if terminal starts are at most N, hence `Q + 34` under
an explicit zero-terminal-start condition. Unconditionally the independent
path/frame decision has `N ≤ 1260`, yielding **Q + 1294**. This is a proved
safe constant, not a claimed optimum. Arbitrary extra frame inputs can even
be recognised initial frames (`arbitrary_frame_can_start`, reusing
`BinDecoderInitialStarts.recognizes_initial`), so the feasibility interface
alone cannot assign all extra frame calls zero starts.

A production port retaining Q+34 needs a theorem about the actual parsed
terminal addresses and their chronological tables, or a different decoder
with a proved density/completion bridge. This work does not add such a
premise to an endpoint.

## Stage 3: recorded log and numeric envelope

Verification in progress.

## Signature accounting and port estimate

No existing theorem signature changes. No premise removal is claimed; the
endpoint signature diff is empty. The eventual port remains unapproved.
Verification receipts are under `evidence/oracle-prereq-20261021/`.
