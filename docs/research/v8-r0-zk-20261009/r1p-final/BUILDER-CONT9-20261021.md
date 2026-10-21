# Builder continuation 9

Branch `codex/cx-builder-ref9-20261021`, base `a2b628d7d`.

**Parts content is complete; the shipped source release remains open.**
The whole-destructor frame and validator/source-admission certificates are
not complete. Source4 retains the runtime and fixed-event execution joins.

## Scope

Continue the D103 destructor boundary, semantic admission, Parts content,
source runtime and fixed-event checker/retry joins. No existing privacy or
quotient module is edited. No production Rust is edited.

## Stage 1: zeroization observation boundary

The exact Charon flag is:

```
--opaque 'crate::state_only_trace::{impl core::ops::drop::Drop for crate::state_only_trace::StateOnlyTraceFoundation}::drop'
```

The resulting LLBC contains exactly one matching `drop`, marked Opaque with
body `"Opaque"`; its implementation is neither deleted nor changed. The
initial audit incorrectly expected JSON null for an opaque body. Fixing that
audit allowed the already generated LLBC to continue; Charon was not rerun.
The proposed alternate-name extraction was cancelled during reservation
waiting and generated no extraction receipt.

The footprint includes all owned Vec buffers. It cannot mean only the inline
`[Vec<M31>;16]` headers. `BuilderDropObservation` proves a sequential heap
specification for arbitrary footprints and byte values: writes stay within
the listed footprint; the result is `ok ()`; observations at disjoint retained
addresses are preserved. J9338: exit 0, 1.26 s, peak 2,533,612 KiB, swaps 0;
five audits use only propext, Classical.choice and Quot.sound. This is a
kernel-checked heap-model rule. Its `P6Route` explicitly requires source
correspondence; it does not claim Kani soundness as a Lean axiom or supply an
unverified source certificate.

Forest extraction now advances beyond `&raw mut` and fails at the frontier
validator: `incremental_merkle.rs:308–343`, `Unexpected return`,
`InterpLoops.ml:169`. Charon: exit 0, 11.444 s, 616,396 KiB, swaps 0.
Aeneas: exit 2, 3.135 s, 458,096 KiB, swaps 0. This remains an exploratory
reference-source extraction with the inherited P6 substitutions/opaque
records and external layer, and the metadata-only PairLeaf constructor
rename. No successful aggregate source certificate is claimed.

Kani actual destructor behavior: `trace_drop_small-scalar` passes 459 checks
(six unreachable), 146.605 s, 3,941,440 KiB, zero swap, arbitrary lengths
0..2 in all 16 columns and arbitrary stored u32 words. It checks unit return,
no panic and an unchanged separately owned output word. This bounded result
is **not** a universal write-set certificate.

The `volatile_zero_word` contract projects exactly the shipped volatile
store through M31's transparent u32 representation. Dynamic frame checking
proves the only permitted target is that word and it becomes zero; 57 checks
(two unreachable) pass, 0.540 s, 168,276 KiB, zero swap. No destructor is
stubbed. This supplies a projected P6 store certificate, composable with the
arbitrary-length heap-model theorem, but a complete actual-Drop/loop mapping
has not been supplied.

Three whole-destructor dynamic-frame experiments were stopped at the 6 GiB
MemoryHigh review, without verdicts: arbitrary small lengths (233.861 s,
6,402,728 KiB), fixed two-word columns (85.461 s, 6,384,000 KiB), and one
symbolically selected two-word column (83.215 s, 6,370,368 KiB). All swaps 0.
Each narrowed a different source shape; none was rerun unchanged or with a
larger cap. SIGTERM was sent only to that task's CBMC child; Kani reported no
successful verification. The earlier explicit-destructor call failed Rust
compilation, the renamed harness selector matched no harness, and the
32-byte output comparison failed a memcmp unwinding assertion. All remain
in the receipts. The final scalar comparison corrects that harness issue
without changing the destructor unwind bound.

## Stage 2: admission

A control-flow reference replaces the frontier loop's early return with a
carried Result and guarded while. It is added only to the existing cfg-only
reference file. Substituting it in the isolated owned constructor advances
forest translation to code generation. Two further constructor name clashes
are fixed in LLBC metadata: enum constructors and tuple struct constructors
receive distinct function names. Function bodies, IDs, calls and type layout
are not changed by those renames. The structural JSON audit finds exactly
five changed scalar leaves, all in function names, the item-name index or
the function rename attribute. Exact before/after values are committed in
`builder-cont9-adaptation-audit.json`. Aeneas then succeeds: 5.667 s,
455,440 KiB, zero swap, 6,625 generated Lean lines. This raw output contains
24 unsupported externals (including Drop, records, lazy external, iterator,
array, Option/Result and slice operations) and is not admitted or compiled as
a certificate.

The full Kani validator comparison with explicit shared-root argument
checks timed out at 240 s with no verdict. Its GNU-time parent RSS is
incomplete (14,960 KiB); it is not the child peak. The replacement projects
the common pure root-helper result. Both callers pass the same immutable
tree and empty table, so this isolates control flow, not root reconstruction.
The projected-root replacement also timed out at 240.040 s without a verdict; its parent RSS is likewise incomplete. Neither failed experiment certifies the reference substitution. The complete semantic admission obligation remains open.

## Stage 3: Parts content

`BuilderInverse` proves the actual modular-exponentiation loop by induction
on the symbolic exponent, with bounds preventing u64 multiplication wrap.
`BuilderInverseResult.inverse` identifies the actual `inv_r` with `invR` for
all u32 storage words. J9343 and J9345 pass (2.31 s / 3,751,128 KiB and
1.78 s / 3,736,720 KiB, zero swaps). The failed monolithic specialization
J9342 reached kernel memory pressure at 7,169,680 KiB; it was replaced by
separate symbolic field-power and scalar-conversion lemmas, not a limit
increase. The generic loop was checked before its concrete specialization.

`BuilderPrimitiveDigests` supplies 46 identities between the actual aggregate
and component block-writer/Poseidon extractions, including all recursive
loops, round constants and full permutation. Recurrences use symbolic suffix
induction with bounds 4, 8, 11 or 16; no concrete permutation cell is
reduced. Its deterministic generator `--check` passes. J9347 passes in
4.55 s, 3,791,660 KiB, zero swap; all 46 axioms audits use only the allowed
standard axioms. This removes duplicated primitive computation as a source
of mismatch.

`BuilderDigestArguments` proves complete Result identities for the actual
note chunks, digest extraction, permutation wrapper, block/sponge/node
hashes, owner, arbitrary chunk and length selection, and chained sponge
pre-states. J9356: 2.92 s, 4,023,840 KiB, zero swap, 16 audits.
`BuilderDigestTotal` proves primitive and arbitrary-note totality for all
raw words without admission hypotheses: J9357, 1.95 s, 4,015,268 KiB,
zero swap, eight audits. The proof uses generic finite-field refinement;
no concrete hash is evaluated.

`BuilderAuxContent` derives the exact change/recipient/input digest maps,
both output occupancy records, the auxiliary callee and the full inherited
Content.aux equation from successful actual Parts. It requires neither a
transfer/withdrawal flag premise nor an assumed digest/inverse equality.
J9359: 2.03 s, 4,013,772 KiB, zero swap, eight audits. All standard axioms.
`BuilderTreeArguments` identifies the full actual membership digest loop
against `treeCurR`, including raw-word bit tests and totality (J9361, 1.96 s,
4,018,700 KiB, zero swap). `BuilderPathContent` proves all four actual path
array closures, their canonical arguments, and full Content.path from
successful Parts (J9363, 3.11 s, 4,018,648 KiB, zero swap). Six and eight
standard-axiom audits respectively. No path-array equality is assumed.

`BuilderAppendArguments` identifies the actual output pair, append cursor
bit, sibling selection and complete append-digest recursion, with totality.
J9365: 2.11 s, 4,018,816 KiB, zero swap, eight audits.
`BuilderBlockArguments` derives all source node-child arguments (J9369,
4.40 s, 4,034,672 KiB, five audits). `BuilderBlockResult` identifies the
complete actual 57-block writer and proves totality (J9372, 2.14 s,
4,020,580 KiB, four audits). All statements are symbolic in raw words.

`BuilderBlockCollect` proves ordered bounded-range collection with a
FiniteTrace induction and derives every block from the actual successful
Parts call (J9374, 2.01 s, 4,029,068 KiB, three audits).
`BuilderPartsComplete.content` supplies **all three** Content fields from
`parts w p = ok pt`; `banks_columns` then supplies the actual merged-bank
flag, every canonical cell and all shipped Vec columns without a Content
premise. J9375: 1.82 s, 4,008,464 KiB, zero swap, two audits.
All these accepted axiom audits contain only the permitted standard axioms.
This completes the remaining Parts content obligation at the existing
aggregate-extraction/std-model boundary. It does not prove semantic
admission or equate the exploratory forest extraction with shipped Rust.

## Stages 4–5: runtime and checker/retry obstruction

The shipped RustRuntimeJoin remains uninhabited here. Parts content now
supplies the entire structural bank/column computation, but successful
shipped forest admission (including append/root and sentinel), complete
Drop/owned-reference correspondence, and the concrete source instance map
remain unavailable. The generated forest reference still contains 24
unsupported externals and its validator equivalence attempts have no verdict.
These are actual source-proof obstructions, not additional assumed joins.

`BuilderRuntimeBoundary.zero_padding` derives an invariant of the exact
RustRuntimeJoin. `no_mismatch_runtime_join` supplies a typed counterexample
to dropping that premise for an arbitrary h: a unit-instance prover whose
padding columns equal one cannot have any such join. J9354: 1.83 s,
4,089,108 KiB, zero swap, two standard-axiom audits. This is not a claim that
the shipped prover has that defect. It explains why replacing the missing
source inhabitant by a theorem for every h would be false.

The source experiments, observer and randomness in the endpoint also remain
arbitrary. The inherited checked BuilderExecutionBoundary counterexample
still prevents deriving a fixed-event ModelExecutionJoin from builder
facts. No concrete P_chk/P_R1, pole/VR1, masks, retry/non-Rejected errors,
publication, serialization or reached-query execution law is constructed.
The real and ideal fixed-event joins are retained; no arbitrary bad event,
canonical-h substitution or fabricated coupling removes them.

`PrivacyR1FinalReleaseSource4` builds on Source3 and imports the completed
Parts and observation/boundary results. Its binders and complete conclusion
are unchanged, including freshness and strict <2^-100. The deletion-only
diff has zero deletions; no weakening or completed source release is claimed.

## Resource and provenance

All task jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
with reservation guards below the host's 55 GiB allowance and the required
linker flag. No other worker is interrupted. No wallet or key cleanup is
performed. No shipped crate/program file changed against the base, so the ELF rule is
not triggered and no unchanged SBF rebuild is repeated. No binary, object,
LLBC, archive or key is committed. No push, merge or full frozen-manifest
replay is performed. The new conditional endpoint receives its own focused
build and axioms audit; no unconditional release verification is claimed.

The early bounded behavior experiment preceded per-run Rust source-pin
capture. Its retained harness bodies are unchanged in the final source,
but no complete input-tree digest was captured at launch; it is supplemental
bounded evidence. The accepted projected volatile-word contract has the
per-run input pins in `builder-cont9-host-evidence.json`. The full forest
input/tool pins and all unsuccessful receipts are retained there too.

## Final focused verification

The read-only audit validates 16 current sources/objects, their direct-import
fingerprints, 129 complete named axioms results and zero swaps. Every accepted
axiom set is a subset of propext, Classical.choice and Quot.sound. Failed
elaborations remain in the JSONL and are excluded by source SHA and dependency
fingerprint. No proof/resource limit was raised. All original privacy,
quotient, runtime-join and release modules are unchanged.

| Target in R1Z | attempt | exit | wall | peak RSS KiB |
|---|---:|---:|---:|---:|
| `BuilderDropObservation` | 9338 | 0 | 0:01.26 | 2533612 |
| `BuilderInverse` | 9343 | 0 | 0:02.31 | 3751128 |
| `BuilderInverseResult` | 9345 | 0 | 0:01.78 | 3736720 |
| `BuilderPrimitiveDigests` | 9347 | 0 | 0:04.55 | 3791660 |
| `BuilderDigestArguments` | 9356 | 0 | 0:02.92 | 4023840 |
| `BuilderDigestTotal` | 9357 | 0 | 0:01.95 | 4015268 |
| `BuilderAuxContent` | 9359 | 0 | 0:02.03 | 4013772 |
| `BuilderTreeArguments` | 9361 | 0 | 0:01.96 | 4018700 |
| `BuilderPathContent` | 9363 | 0 | 0:03.11 | 4018648 |
| `BuilderAppendArguments` | 9365 | 0 | 0:02.11 | 4018816 |
| `BuilderBlockArguments` | 9369 | 0 | 0:04.40 | 4034672 |
| `BuilderBlockResult` | 9372 | 0 | 0:02.14 | 4020580 |
| `BuilderBlockCollect` | 9374 | 0 | 0:02.01 | 4029068 |
| `BuilderPartsComplete` | 9375 | 0 | 0:01.82 | 4008464 |
| `BuilderRuntimeBoundary` | 9354 | 0 | 0:01.83 | 4089108 |
| `PrivacyR1FinalReleaseSource4` | 9376 | 0 | 0:03.28 | 4117480 |

The exact source revisions (including dirty-input flags), SHA-256s, tool and
environment pins, caps, full audits and receipt bindings are committed in
`builder-cont9-final-audit.json` and `builder-cont9-attempts.jsonl`.
No task-owned Rust/Kani/Aeneas build is left running. Remaining work is the
universal source destructor/owned-validator correspondence, the 24 forest
externals and semantic admission, then the concrete runtime and actual
checker/retry/observer couplings. The complete Parts handoff needs no further
Content assumption.

## Verbatim endpoint signature audit

No complete runtime or execution join was discharged. The binder/conclusion
diff is empty, excluding the theorem name: deletion-only with zero deletions,
not a strict weakening. No new or stronger premise is introduced. The error,
freshness term and strict <2^-100 conclusion are byte-identical.

Before, verbatim:

```lean
theorem privacy_R1_release_source3
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B)
    (R_source_records_admission_banks_transport : BuilderRuntimeJoin.RustRuntimeJoin h)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : (h).Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : (h).Instance),
      (h).public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 (h).transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (h).transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 (h).transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (h).transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE (h).transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1)) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) < 1 / 2^100
```

After, verbatim:

```lean
theorem privacy_R1_release_source4
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B)
    (R_source_records_admission_banks_transport : BuilderRuntimeJoin.RustRuntimeJoin h)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : (h).Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : (h).Instance),
      (h).public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 (h).transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (h).transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 (h).transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (h).transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE (h).transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1)) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) < 1 / 2^100
```
