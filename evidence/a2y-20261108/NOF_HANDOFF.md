# NOF A2 handoff (Stream A, job NOF_)

**The A2 field compiles.** In Lean:

```lean
AspisR1.NOF_A2Field.field {W Tx} (L0 copy std) :
  RSL.TAS.NND_A2 (AspisR1.NNH_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
    NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0
```

It has a delivered-type `rfl` example (NOF_A2Field.lean, L012). The raw ax2 walk with ledger30's
pinned walker is standard-only (L014). The coherent combined import NOF_FinalCombined passes (L013).

Branch codex/cx-a2-20261107 (merged with research 8e24e017860); receipts in evidence/a2y-20261108/NOF_*.
Budget for the first delivery: **14 of 20 capped scopes, 0 Kani, 0 extraction.** Of these, 9 had exit 0 and 5 failed. The follow-up (below) brings the total to 18/20.

| stage | cap | used |
|---|---|---|
| P0 | 3 | 2 |
| P1 | 4 | 2 |
| AUDIT | 2 | 1 |
| P2 | 6 | 5 |
| P3 | 2 | 1 |
| P4 | 5 | 3 |

## Delivered constants (all axioms: propext, Classical.choice, Quot.sound; canonical_of_early: none)

| item | constant | scope |
|---|---|---|
| P0 | package-view repair (NOF_P0_VIEW.json); unchanged RawCircleSampleActual{FallbackCoordinates,PolicyUnconditional}V1 rebuilt byte-identical to the cache | L001, L002 |
| P1 | `AspisR1.NOF_PowersAssociation.source` (+ identify, canonical_gamma, canonical_early, canonical_of_early, decode_link) | L004 |
| audit | NOF_SLOT_AUDIT.md: no seed `.div` slot (stage op4/op7/op8/op12, adapter op21/op24) is reached | L005 |
| P2 | `AspisR1.NOF_CommonConverse.common` (+ source_run, tail_transport) | L010 |
| P3 | `AspisR1.NOF_Tx2Op11.tx2Op11 : NNH_ExactRemainingTypes.tx2Op11` (exact merged type) | L011 |
| P4 | `AspisR1.NOF_A2Field.field` (+ sdk_at_slot, reserved_at), rfl example | L012 |
| combined | `NOF_FinalCombined` imports NNY_FinalCombined (run-6 + NNU + all NNY) and all NOF proof modules | L013 |
| raw ax2 | field, tx2Op11, common, PowersAssociation.source, sdk_at_slot, reserved_at: walked = collected = {Classical.choice, Quot.sound, propext} | L014 |

P1 statement: `NID_ResumeFields.Domain p a → NHT_PacketOps.powers 29#usize p.gamma = ok out → Tx2N_Powers.powers 29#usize p.gamma = ok out`.

P2 statement: from `NJC_FilledClause.reserved r = env.reservation`, `Dom064 V0 (bytes pub,bytes proof,bytes ck)` and
`LIBB_Tx2EnvCode.code env pub proof ck = .ok (.Ok ())`, conclude
`VTop_Stages.verifier.candidate.tx2_common (NNH_Tx2SlotTransport.stage m env err r)
 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r)) pub proof ck () none = .ok (.Ok ())`.
- This is exactly the NNY_REMAINING Y2 conclusion, plus the same hypotheses as the merged tx2Op11.
- Proof: a step-by-step simultaneous walk of the source run (restated as the VTop body over the source dictionary by rfl lemmas NHT_Tx2CommonModel.source / NJJ_Common.source) and the installed body.
- Each reached call is transported at its reached arguments:
  - resume: NNH_ResumeOkPort.value;
  - powers: NOF P1;
  - inactive: NNU_Inactive.source;
  - Merkle: NNU_MerkleSlots.installed + NNY_NNUParent.parent (NodeLeaf by NNY_MerkleShared.tx2);
  - geometry: NNU_Geometry.source;
  - pending: NNH_Tx2LiteralSlots.pending + LIBB_Tx2Reservation.reserved;
  - query: NNU_Query.source;
  - flush and constants: NNH_Tx2LiteralSlots;
  - finish: NNH_Run5bFinishEdge.selected.
- No whole-common equality premise is used.

P4 route:
1. The EnvRep conjunct gives env = Run5bCtx.envOf c (NNH_Run5bCtx.env_unique) and the reservation representation (reserved_at).
2. The selected child arguments are carried to the NND carrier by NNH_PhysicalCarriers.
3. NNY_Stage2PacketResidual.returned (NNU_Stage2Tail.returnedCuts / NNH_Stage2To064 + NNY_Stage2Residual.continuation_iff) gives the SAME packet/segment, Dom064, source success and the op11 iff.
4. The iff is applied to NOF_Tx2Op11.tx2Op11 at the host seed m0.
5. sdk_at_slot (NNH_Run5bCtx.missing_at_slot) identifies that SDK with the host's `sdk c`.

Deviation from the brief, recorded: S_host's ModelRet2 has the NNH_AcceptanceSig.physical shape, not AMN's `withMin` shape.
- toNND_A2/viaReturns2 therefore do not apply to this Sig.
- The field is built directly. It demands only the returned-Ok arm at the selected child arguments, so no Returns evaluator (NNY_JunkAudit.value) is needed.
- This removes no obligation: the field's type is the exact one requested (rfl example).

## Assumptions

- Discharged: tx2Op11 (now a theorem), the Y2 common converse, the powers association, and the A2 field itself.
- Retained: those already inside the merged modules used. EnvRep/Exhibited are field binders, not added premises; Exhibited is unused.
- Added: none.
- No Root0, Realizes-as-premise, hash-injectivity, success, representation or selector premise.
- No verifyState_eq.
- NodeLeaf is discharged by theorem.
- The adversary/context is universal.
- RSL and library carriers are unchanged.
- No NOF theorem depends on currentBase (op1), stage op4/op7/op8/op12 or adapter op21/op24: all quantify over an arbitrary seed `m` or use the host seed only through compiled slot theorems.

## Validation

- Every scope ran under v4.32.0 with `lake env lean -j1 -M7000 -DElab.async=false`, 180 s, MemoryHigh 6G / MemoryMax 8G / MemorySwapMax 0 / TasksMax 64.
- Every launch had admission exit 0 AND allowed:true, a whole-host scope count < 6 with lean processes < 6, and disk >= 40 GB.
- Scopes ran one at a time.
- Max peak RSS was 7053056 KiB (L014); swaps 0.
- L010's launcher SSH dropped after submission. Its receipt was recovered read-only and the scope was not resubmitted.
- Exact receipts: NOF_COMPILE.tsv, NOF_ATTEMPTS.jsonl, NOF_Lnnn/receipt.json. Each has target, argv, source revision/hash, dependency pins, exit, wall, RSS, swap and printed axioms.
- Failed scopes, all uncredited (their failed-declaration sorryAx is a failure, never credit):
  - L003: import conflict;
  - L006–L009: four P2 proof-mechanics fixes, each a changed proof.
- Raw ax2: walker NNM_ProofDriver sha256 46ee271b…ca3c (same binary as ledger30 L008). Reachable lists are in NOF_audit/*.xz with sha256.
- Walker fixtures: the eight passing ledger30 fixtures for this identical binary are reused, not rerun.
- This is focused cached validation, not a frozen-release replay.

## Follow-up: corrected host (NOC seed), P5, 4 of 4 scopes

```lean
AspisR1.NOF_A2FieldCorrected.field {W Tx} (L0 copy std) :
  RSL.TAS.NND_A2 (AspisR1.NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
    NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0
```

It compiles with the same delivered-type `rfl` example (L016). The axioms are propext, Classical.choice and Quot.sound.

**Shape check:** NOC_Run5bHost.S_host is built exactly like NNH_Run5bHost.S_host:
- the same NNH_RecordSig.physical / NNH_AcceptanceSig.physical / NNH_HostEnv.install over identical `data`/`hostRuntime`;
- so ModelRet2 and EnvRep have the same shape;
- only model2's `sdk c` changes, to `NOC_HostCtx.sdk c`, whose seed is `NOC_HostSeed.m0 (envOf c).reservation`.

The transfer is a re-instantiation. The seed-generic theorems are reused unchanged:
- NOF_Tx2Op11.tx2Op11 at m := NOC_HostSeed.m0 ρ;
- NNY_Stage2PacketResidual.returned;
- NOF_A2Field.reserved_at;
- NNH_Run5bCtx.env_unique (same Ctx and EnvRep).

There is no NOC analogue of NNH_Run5bCtx.missing_at_slot. So:
- `NOF_A2FieldCorrected.clockFree` restates NNR_ClockFree.M1b for an arbitrary seed, using NNR_ClockFree.residual and modelSlots, which are already seed-generic;
- `NOF_A2FieldCorrected.sdk_at_slot` is the NOC sdk identity.

Scopes:
- L015 failed: carrier namespace not opened (`Bytes`); fixed by opening the namespaces that NNR_ClockFree opens. Uncredited.
- L016 passes.
- L017: `NOF_FinalCombined2` = NOF_FinalCombined (L013, left unchanged so its pin stays valid) + NOF_A2FieldCorrected. Passes and prints all four new audits.
- L018: raw ax2 on the new root only, with the same pinned walker. For `AspisR1.NOF_A2FieldCorrected.field`, walked = collected = {Classical.choice, Quot.sound, propext}, with 58812 reachable constants. Output is in NOF_audit2/*.xz with sha256.

Overlay for the corrected field: LEAN_PATH = NOF_objects, NNY_objects, then NOF_EXTRA_PATHS.json, then NNY_RUN5B_PATHS.json.
- NOF_EXTRA_PATHS.json holds the read-only references codex-cx-a1-20261108/NOC_objects, NNX_objects and NNV_objects.
- The import preflight found only three extra duplicate names. All are automatically generated `eq_1`/`congr_simp` lemmas of the kind already present in the passing baseline.

Budget for the whole job: **18 of 20** capped scopes (L001–L018), 0 Kani, 0 extraction.

## Overlay for G0 FINAL

/home/dombarker/project-offloads/codex-cx-a2-20261108/NOF_objects, prepended before NNY_objects and NNY_RUN5B_PATHS.json. Object hashes are in NOF_OVERLAY.json.

## Failed approaches retained

- The historical FIp_PowersValue closure conflicts with the NNU (RPz7_) closure; use the in-closure RPu/RPt replays instead.
- simp does not reduce the tuple-let match in the VTop body; the head is reduced by whnfHeadPred.
- The installed op2 is the library decoder (use NNU_Inactive.source).
- Case-splitting a variable after a later `obtain` reintroduces a stale hypothesis under the current name.
