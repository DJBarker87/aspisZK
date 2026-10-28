# TX2 fixture work — in progress

Stage 1 partial (updated after the complete decoder proofs): all seven PDA value observations are checked, conditional only
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

## Stage 1 decoder milestone

All three observations are now unconditional kernel theorems:

```lean
JHu_Master.observation :
  NCV_Install.op48 JHg_DataMaster.value = ok (.Ok JHg_AccountValues.master)
JHu_Checkpoint.observation :
  NCV_Install.op49 JHg_DataForest.value = ok (.Ok JHg_AccountValues.checkpoint)
JHu_Lane.observation :
  NCV_Install.op50 JHb_DataLane.value = ok (.Ok JHg_AccountValues.lane)
```

These are the ORIGINAL E008 `NCV_Reference` bodies selected by NCV_Install,
with its original lossless carrier conversion and error mapping. They have no
SHA, PDA, reader-success, acceptance, source-refinement or native-equality
premise. The supplied CastRef helper results were adapted by proving the
original E008 byte and word readers symbolically, then proving its original
sequence and digest loops by NCV array-frame induction. No unproved equivalence
between E008 and E010 was introduced. Policy/identity and master state checks
are composed on bounded fields; the lane uses named digest fields and twenty
scalar occupancy cases. No full-buffer normalization or decoder `decide` occurs.

JHu_FrontierRun repairs the predecessor generic frontier proof: a literal's
elaborator-generated bound proof produced `No goals to be solved`; naming the
existing scalar bound `(8#usize).hBounds` in `Usize.ofNatCore` resolves it.
This is a source-proof fix, not a tool/launcher/option change or cap increase.

JHu_Authentication.source composes all SIX available outer children on
`JHd_ReferenceSlots.install (NCV_Install.install base)` with the original
JHg world, buffers, account records and slot. Its exact remaining premises are:

1. `runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base`.
2. The original whole registry child, on that SAME dictionary:

```lean
registry : AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
  (JHd_ReferenceSlots.install (NCV_Install.install base))
  CPH_Program.verifier JHb_Programs.pool (JHg_World.e2.snapshot 1 384 384)
  JHg_AccountValues.master (JHg_World.e2.snapshot 4 128 256)
  (JHg_World.e2.snapshot 5 192 320) slot = ok (.Ok ())
```

The conclusion is the exact inherited authenticate_asq8_accounts success,
not wrapper acceptance. The source/body installation specializes free op48/49/50
under ruling (s); base and slot stay universal. Removing six local child
observations under this specialization does not remove any headline premise.
The full printed statement and all current top-theorem axiom lists are in
JHu_040/stdout.log. JHu_REGISTRY_GAP.json retains the tracked-definition
search, current/legacy excerpts and hashes. It is not a claim that constructing
a current model is impossible.
