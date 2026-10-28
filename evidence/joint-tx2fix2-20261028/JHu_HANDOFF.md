# TX2 fixture handoff — 2026-10-28

**Partial Stage 1: six of seven outer authentication children closed.
JHu_TX2.accepted2 and JHu_Joint are NOT established.**

Branch: `codex/cx-joint-tx2fix2-20261028`. Commits so far:
`3207e3bc6e` (PDA/checkpoint milestone), `de5e4f6df9` (master/lane and six-child
composition). A final evidence-only commit follows this handoff. No push.
Only new JHu_ modules and this evidence directory changed.

## Exact established claims

These three complete observations are unconditional kernel theorems:

```lean
JHu_Master.observation :
  NCV_Install.op48 JHg_DataMaster.value = ok (.Ok JHg_AccountValues.master)
JHu_Checkpoint.observation :
  NCV_Install.op49 JHg_DataForest.value = ok (.Ok JHg_AccountValues.checkpoint)
JHu_Lane.observation :
  NCV_Install.op50 JHb_DataLane.value = ok (.Ok JHg_AccountValues.lane)
```

They evaluate the ORIGINAL E008 `NCV_Reference` bodies selected by NCV_Install,
with its original lossless carrier conversions and error mapping. Their
premise lists contain no SHA, PDA, reader success, acceptance, native equality,
or source-refinement hypothesis. They are reference-model fixture results;
no missing native/P6 equality from NCV is discharged or assumed here.

The NCV symbolic fixture support used E010/CastRef, not the installed E008.
This job proves the E008 byte-copy and word-reader field laws directly, then
uses array-frame induction for its original sequence and canonical-digest
loops. Master identity, policy, reserved fields, nonzero and chronology checks
are composed symbolically. Lane uses twenty named digest observations and
scalar occupancy cases at next index 13. There is no assumed E008/E010
whole-decoder equivalence, no full-buffer normalization and no decoder decide.
Tiny scalar guards and bounded eight-limb table-row selections are separate
from decoder evaluation. `JHu_generate_frontier.py --check` reproduces the
checked frontier observations byte-for-byte, permanently emitting named
field-law applications for every row.

JHu_FrontierRun also repairs the predecessor frontier proof's literal-bound
elaboration failure (`No goals to be solved`): the nested width now uses
`Usize.ofNatCore 8 (8#usize).hBounds`. No depth/heartbeat override, tool change,
launcher change or cap increase was introduced.

JHu_PdaObservations proves all SEVEN fixture PDA returns using the inherited
unconditional JHs digest equations and JHt off-curve certificates. Its sole
propositional premise is the exactly named
`JHu_FixturePdaRuntime.FixturePdaRuntime base`. Its definition is:

```lean
def FixturePdaRuntime (base : AdapterRw.Ops) : Prop :=
  ∀ seeds program, Call seeds program →
    base.op38 seeds program = JHs_PDA.derive seeds program
```

Call has exactly seven constructors: master, checkpoint, lane, registry,
registryProgramdata, entry, verifierProgramdata, each at the original JHs seed
and program arguments. The definition's documentation reproduces the complete
FixturePdaRuntime statement text from JHs_TRUST_PROPOSAL.md verbatim. The Lean
proposition is that statement's value projection on those valid fixture calls;
ABI/memory/compute conditions are the quoted conditions, not newly proved
facts. This is an explicit hypothesis, never an axiom or an adopted trust row.
It supplies neither a digest/off-curve certificate nor decoder/caller success.
Owner runtime/artifact adoption remains pending.

## Before / after and exact remaining hypotheses

Before, JHj_Authentication.source retained seven observations: master decoder,
master PDA, complete registry authentication, checkpoint decoder, checkpoint
PDA, lane decoder, lane PDA, all on JHd_ReferenceSlots.install base.

After, JHu_Authentication.source checks the original complete outer caller on
`JHd_ReferenceSlots.install (NCV_Install.install base)`, with the SAME JHg world,
actual buffers, decoded records, keys and slot. Its only remaining premises,
besides universally quantified base and slot, are:

1. `runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base`.
2. The original complete registry child, on that SAME dictionary:

```lean
registry : AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
  (JHd_ReferenceSlots.install (NCV_Install.install base))
  CPH_Program.verifier JHb_Programs.pool (JHg_World.e2.snapshot 1 384 384)
  JHg_AccountValues.master (JHg_World.e2.snapshot 4 128 256)
  (JHg_World.e2.snapshot 5 192 320) slot = ok (.Ok ())
```

Its conclusion is:

```lean
AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
  (JHd_ReferenceSlots.install (NCV_Install.install base)) CPH_Program.verifier
  (JHg_World.e2.second S2W_D189Wrappers.secondSizes)
  JHb_Programs.pool 3#u8 slot = ok (.Ok JHg_AccountValues.value)
```

NCV_Install fills only the three free op48/49/50 fields under ruling (s).
No acceptance or desired-output hypothesis is hidden in their definitions.
The registry observation is explicitly retained, not relabelled as a SHA or
runtime certificate. Six LOCAL child observations are discharged under this
specialization; no arbitrary-base headline premise is claimed removed.
The existing deployed headline, security contract and source/artifact/trust
qualifications are unchanged. The 100-bit target remains not established.

## Blocker and next deliverable

The supplied new decoder inputs cover op48/op49/op50, not the registry and
entry decoders op33/op34. Those remain external declarations in the current
cohort, and NCV_Install leaves them unchanged. JHr_EXTERNAL_SLOTS.json already
identified that separate gap; its original absence was not resolved by NCV.

A tracked-tree search for Lean definitions of decode_verifier_registry_v2 and
decode_verifier_registry_entry_v2 finds only the older August 31
V7RegistryV2ProductionCodecs extraction. That decoder requires byte 7 to be
zero; the current Rust decoder reads the bump there, and JHg_AuditRegistry.bump
proves this fixture contains 255. The old body cannot supply the required
success, and no unproved source equivalence is adopted. JHu_REGISTRY_GAP.json
records the exact search, current/legacy excerpts, paths and hashes. This is
not a claim that a current model cannot be constructed elsewhere. A current
model or authorized reference extraction was requested during work; no reply
was received before this handoff.

Next: provide current-format op33/op34 reference bodies with their cohort
carrier/error conversions, prove their fixture results, then compose the
existing policy/status/loader and registry/entry continuations with the FOUR
proved registry PDAs. That closes the seventh JHj child. Actual validate_asq8
and same-SDK wrapper composition must then be checked before accepted2.

Stages 2 and 3 were not entered. No theorem with the requested
SHA-certificates-plus-FixturePdaRuntime-only accepted2 statement is supplied;
adding registry success to such a theorem would miss the requested goal.
JHe_SHARealization's 453 tree equations are retained unchanged in TX1;
JHi's three byte-SHA proofs and JHq_TX1.accepted1_saved are reused only as
existing evidence, not newly composed here. The requested TX2 target is still:

```lean
S2W_D189Wrappers.second (JHe_Natives.second base stage)
  CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
  JHb_DataRequest.value (.Ok slot) () = ok (.Ok (JHg_World.e2.heap,()))
```

No independent checkpoint or TX1 output was selected. JHn_ExactReturned and
JHq_TX1's SAME saved bytes remain JFx_NativeBytes.checkpoint, unchanged.
JHn_Joint.assembleJoint consumes ByteIdentity and accepted2, not an
accepted1_saved proof directly. No Stage 3 import/cap failure occurred, so
there is no Stage 3 peak or basis for requesting the lead's 16 GiB scope.

## Validation and resource receipts

Budget used: **40/80 Lean, 0 Kani; 25 pass, 15 rejected attempts**. This is a
source-input blocker, not budget exhaustion. Every current module has an
exact-source passing receipt. Rejected drafts/error-placeholder audits receive
no credit. JHu_VALIDATION.json matches all 25 current modules to receipts,
checks all admissions and limits, and matches all 72 new top-theorem names to
the final audit. Every accepted theorem uses only propext, Classical.choice,
Quot.sound. JHu_ATTEMPTS.jsonl retains each command, source revision/hash,
direct dependency/tool hashes, status, wall time, RSS, swap and full audit/error
output; immutable source snapshots and raw logs accompany every attempt.

Final focused closure audit: JHu_Audit.lean, JHu_040, source revision
3207e3bc6ec94808da48c94c70b9f2aaf4103747 with dirty exact-source snapshots;
exit 0, wall 2.8605893660569564 s, peak RSS 5,686,108 KiB, swaps 0.
All attempts: total Lean wall 84.57936640188564 s; max RSS 5,715,008 KiB;
all swaps 0. Limits throughout: Lean -M7000, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64; one capped scope at a time. Admission always
required allowed:true AND exit 0. No admission/transport retry, timeout,
memory kill, enlarged cap or unchanged pressure-failed rerun occurred.

The assigned JHr cache did not yet exist (its job stopped at feasibility);
it was initialized at /home/dombarker/project-offloads/codex-cx-tx2fix-cache-20261028.
Unchanged lead S2W launchers were copied there. No build/launcher/monitoring
infrastructure was changed. JHu_007's missing Mathlib object was this job's
LEAN_PATH ordering error: its partial tree shadowed complete Mathlib.
JHu_008 corrected that own environment input and passed (rule 11).
JHu_CACHE_PINS.json records all retained own objects and unchanged launcher
hashes. No inherited cache or own retained cache was deleted.

No cold dependency build, full frozen-manifest replay, Kani/Rust/SBF/runtime
gate, source-to-ELF claim, wallet/key operation, other-worktree edit, push or
merge occurred. The final audit reuses pinned compiled dependency caches;
it is not a fresh frozen-release rebuild. Generator validation and focused
proof/bridge/axioms checks are complete; authored files pass whitespace checks.
Raw prover/launcher logs preserve their original emitted whitespace. Evidence
contains no file over 20 MB and no binary/olean/ELF/corpus/archive copy.
