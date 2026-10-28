# TX2 fixture work — in progress

Stage 1 partial: all seven PDA value observations are checked, conditional only
on the single `JHu_FixturePdaRuntime.FixturePdaRuntime base` hypothesis.
Its exact seven-call value projection and verbatim trust-proposal text are in
`lean/JHu_FixturePdaRuntime.lean`. It is never an axiom or an adopted trust row.
JHs SHA equations and JHt off-curve certificates are reused unconditionally.

The E008 checkpoint observation is checked unconditionally:
`JHu_Checkpoint.observation : NCV_Install.op49 JHg_DataForest.value =
 ok (.Ok JHg_AccountValues.checkpoint)`.
Original E008 byte/word/sequence/digest loops are proved symbolically; NCV's
CastRef fixture laws are not silently reassigned to the installed reference.
Every successful top theorem has only standard axioms. Rejected drafts and
error-placeholder audit output are excluded; exact receipts are retained.

Before: JHj_Authentication.source retains seven explicit child observations.
After so far: checkpoint and three outer PDA children have proofs under the
selected decoder body and explicit runtime hypothesis; the four registry PDA
calls also have proofs. Master/lane and complete registry authentication are
still open. No accepted2 or joint result is claimed.

Current blocker: op33/op34 still have no supplied current-format decoder bodies.
The legacy V7RegistryV2ProductionCodecs extraction tests byte7=0, while
JHg_AuditRegistry.bump proves byte7=255 on this fixture. It cannot be silently
installed for a current-format success. A current decoder/reference body or
an explicitly authorized extraction is required. The lead has been asked
while independent proof work continues.

All compiles use the unchanged lead S2W launchers copied to the assigned cache,
6G/8G/swap0/TasksMax64 and Lean -M7000, one scope at a time. Admission requires
allowed:true and exit0. The initially nonexistent JHr cache was initialized;
no inherited cache was deleted or modified. JHu_007 failed because this job's
LEAN_PATH placed a partial Mathlib tree before the complete one; JHu_008
corrected that own environment input and passed. No build infrastructure was
modified. No Kani, wallet/key operations, push or existing proof edits.

Further stages and final validation will be appended before delivery.
