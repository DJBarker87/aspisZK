# TX2 fixture composition handoff — 2026-10-28

**Partial: Stage 1 complete; Stage 2 validates the actual request on the SAME
TX1 SDK, but the wrapper composition exceeds -M7000 at import. accepted2 and
the joint theorem are NOT established. Stage 4 was not entered.**

Branch `codex/cx-joint-tx2fix3-20261028`. No push. Changes are only new JHv_ Lean
modules and this evidence directory; no existing proved module was edited.

## Stage 1 — seventh authentication child closed

Before, JHu_Authentication.source retained the entire registry authentication
child, plus FixturePdaRuntime. After, the exact checked statement is:

```lean
JHv_Authentication.source (base : AdapterRw.Ops) (slot : U64)
  (runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
  AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
    (JHd_ReferenceSlots.install (JHv_Leaves.install base)) CPH_Program.verifier
    (JHg_World.e2.second S2W_D189Wrappers.secondSizes) JHb_Programs.pool 3#u8 slot =
      ok (.Ok JHg_AccountValues.value)
```

JHv_Registry.source composes the seventh child from the original JHj_ policy,
read, PDA, status and entry continuations. All four registry PDAs use the
existing JHu_PdaObservations results; the three account decoders, other three
PDAs and remaining authentication caller are reused unchanged from JHu_.
NCX_JHuObservations supplies the current-format op33/op34 observations.

This is a specialization to explicit total source interpretations, not removal
of arbitrary-base premises for all possible dictionary interpretations:
JHv_Leaves.install installs the existing NBX policy/status value functions,
the canonical upgradeable-loader ID, and NCX/NCV decoder interpretations.
The loader constant's identity with the fixture field is proved using the
existing JHg_AuditRegistry.loader law. No successful authentication or decoder
callback is invented. FixturePdaRuntime is the SAME original seven-call law,
retained as a hypothesis, never an axiom or newly adopted runtime trust row.
No cryptographic or native source-refinement assumption was added/discharged.

## Stage 2 — actual validation and same SDK checked

JHv_Configuration.adapter base selects JHd_ReferenceSlots over JHv_Leaves and
installs the existing full-input JHf_Scan.source, JHf_ReconstructionSlot.source
and JHb_EmitAdapter.source. The emitter remains the explicit return-data model.

JHv_SameSdk.configuration proves the predecessor JHi installation is idempotent
on JHv_Configuration.seed. JHv_SameSdk.sdk proves:

```lean
DrvC_Installation.sdk
  (JHi_Configuration.value (JHv_Configuration.seed base stage) ()) =
  JHe_Natives.sdk (JHv_Configuration.adapter base) stage
```

This is checked configuration coherence, not a native P6 bridge. A whole-config
normalization hit the heartbeat limit at JHv_020; its replacement splits off
the adapter projection, uses JHf_KeyEq.key and JHe_FinalInstallation.config_ext,
then applies the existing final-installation theorem. No heartbeat/depth or
memory cap was raised. The inherited JHe_FinalInstallation object was missing:
JHv_019 recompiles its UNCHANGED source in our own cache, rather than re-proving
it or editing its original source/owner.

Before, JHi_Validation.source retained actual authentication. After:

```lean
JHv_Validation.source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops)
  (slot : U64) (runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
  AdapterRw.r1_pool_adapter.owned.validate_asq8
    (JHe_Natives.sdk (JHv_Configuration.adapter base) stage)
    CPH_Program.verifier (JHg_World.e2.second S2W_D189Wrappers.secondSizes)
    JHb_DataRequest.value (.Ok slot) = ok (.Ok JGx_Validated.value)
```

Authentication, current registry/entry records, scan, reconstruction and raw
terminal validation are all composed, using the original corrected records.
There is no independent checkpoint or TX1 output selection. JHg_World.e2 and
its SAME JFx_NativeBytes.checkpoint-backed saved bytes are unchanged. This job
has not composed JHq_TX1.accepted1_saved or JHn_ExactReturned.source.

## Exact resource blocker and remaining deliverables

JHv_027 targets **JHv_Wrapper.lean**, combining JHv_Validation with JHi_TX2's
existing verifier/finish/wrapper proof environment. It exits **134**, wall
**5.961092847 s**, peak RSS **7,226,936 KiB**, swap **0**, with:

```
lean::memory_exception: excessive memory consumption detected at 'interpreter'
```

No theorem or axioms output was produced. It is excluded. The exact immutable
source is JHv_027/sources/JHv_Wrapper.lean; a convenience copy is under drafts/.
This is a Stage 2 import failure, NOT the Stage 4 exception authorized for the
lead's agg16 runner. No larger-cap or unchanged retry occurred.

Read-only source graph inspection found 5892 module names in this union.
An import-narrowing candidate is retained as JHv_PROPOSED_IMPORT_TRIM.patch,
UNAPPLIED and UNCOMPILED. JHv_IMPORT_DIAGNOSIS.json shows it removes only one
module: required definition owners pull the large closure back in. It is
rejected as an adequate fix. No sufficient in-scope import split was found.
JHv_RESOURCE_BLOCKER.json records this finding and the actual limits.

Next concrete deliverable is an owner-coordinated source/environment factoring
that makes this exact wrapper union fit, followed by the wrapper application.
It must preserve original declaration ownership and SDK definitions; merely
renaming/restating the failed root or raising its cap is not a proof repair.

Stages 3/4 are not checked. drafts/JHv_ByteSHA.lean.txt and JHv_TX2.lean.txt are
UNCOMPILED preparation only, with no proof credit. The intended accepted2 uses
only the existing 453-tree JHe_SHARealization certificate and FixturePdaRuntime;
the three byte-SHA fields would be supplied by JHi_SHAProof/Public/Checksum.
The draft also exposes the stronger runtime-only TX2 implication, since those
three byte equations already have separate proofs. Neither implication is
claimed established here. The joint theorem must still apply JHn_Joint.assembleJoint
with JHn_ExactReturned.source and accepted2 and connect JHq_TX1.accepted1_saved.
No accepted2, SHA, PDA or native success was substituted as a hidden hypothesis.

## Validation, receipts and retention

**28/80 submitted attempt IDs; 26 actual Lean processes; 19 passing results,
9 excluded/failed submissions; 0 Kani.** This is not budget exhaustion.
Two exclusions are own-input launcher preflights with no Lean process (005:
missing corrected predecessor; 018: missing inherited FinalInstallation object).
They were corrected under rule 11. Early local quoting/config-write mistakes
also preceded Lean and obtained no proof credit. No transport/admission retry.

Final focused closure/axioms audit: **JHv_Audit.lean, JHv_028**, source revision
`4b3be47f50` plus exact dirty-source snapshots, exit **0**, wall
**3.330578390 s**, RSS **6,422,612 KiB**, swaps **0**. All **23** completed
statements use only propext, Classical.choice, Quot.sound. Failed-draft sorryAx
outputs are retained and excluded. JHv_VALIDATION.json matches every canonical
new module to an exact-source passing receipt and verifies accepted axioms,
admission allowed:true, and cgroup limits. Total Lean wall 179.966764138 s.

Every scoped job: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
Lean -M7000, one scope at a time; admission requires allowed:true AND exit 0.
JHv_ATTEMPTS.jsonl and per-attempt sources/logs record commands, revisions,
hashes, direct dependency/tool pins, exit/wall/RSS/swap and full axiom/error
output. Launch failures have null process metrics, not fabricated Lean results.

JHv_CACHE_PINS.json inventories retained own objects and unchanged launchers in
/home/dombarker/project-offloads/codex-cx-tx2fix-cache-20261028. No cache was
deleted. No cold dependency/package build, frozen-release replay, runtime/Rust/
Kani/SBF/ELF gate, wallet/key operation, external-worktree edit, push or merge.
NCX's native P6 gaps, deployed headline/trust qualifications and 100-bit target
remain unchanged. This is focused fixture-model evidence, not deployed security
closure; **the deployed target is not yet established**.
