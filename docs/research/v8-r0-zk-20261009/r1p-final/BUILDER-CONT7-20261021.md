# Builder continuation 7

Branch `codex/cx-builder-ref7-20261021`, base `b7a4cc502`.
No push or merge. Work and evidence are recorded incrementally.

## Stage 2: canonical Parts / column handoff

`BuilderPartsContent.canonical_merge_cell` proves raw canonical split/merge
preserves every copyCell for arbitrary records, with no WitnessOk or PubCorr
assumption. `cell_eq` transports componentwise block/path/aux correspondence
to the actual Parts dispatcher. `banks_columns` composes that transport with
the actual full-bank materialization and column-major readout, including
thirteen zero padding columns. The proof is symbolic; no cell enumeration.

The primitive `Content.blocks`, `.path`, and `.aux` obligations remain.
It does not yet prove actual Parts computes canonical components.

The actual shipped `columns` function has now been extracted separately.
`BuilderColumnsExtracted` uses the same three proved std adapters as the
bank extraction (from_fn, iterator map, mapped next), removing the backend's
unsupported map/collect trait metadata only. No Rust function body is
modified; no external declaration remains. Charon exit 0, 9.912 s,
611,788 KiB RSS; Aeneas exit 0, 0.292 s, 75,504 KiB RSS, zero swaps.
The retained first CLI attempt rejected an incorrect preset before building;
the corrected command is separately recorded. Adaptation audit:
`builder-cont7-columns-adaptation.json`.

`BuilderSliceCollect` proves ordered slice iteration and identity-map Vec
collection by symbolic suffix induction. `BuilderColumns` proves total
execution of every actual column closure and the complete actual columns
function, all sixteen column lengths, all 1,024 row reads per column, and
the thirteen padding columns. `source_banks_columns` composes the actual
Parts, bank materialization, merge, and Vec wrapper into the canonical raw
copyCellMerged handoff, conditional on the primitive Content facts. There
is no Vec/array equality or successful columns execution hypothesis.

Final focused attempts 9313, 9315, 9319: extraction, generic collector, and
full dependent bridge. All standard axioms, zero swaps; final bridge wall
2.49 s, peak RSS 4,033,244 KiB. Retained failed elaborations 9314, 9316,
9317 are corrected source versions, not accepted certificates.

Env J 9308: target `R1Z.BuilderPartsContent`, exit 0, wall 2.75 s,
peak RSS 4,006,804 KiB, zero swaps. All three #print axioms audits use only
propext, Classical.choice, Quot.sound. Exact source/dependency fingerprint,
revision and complete logs: `builder-cont7-attempts.jsonl`. New module;
no shared source/object replaced. Compiled with the task-owned run-joint.sh,
-M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.

## Stage 1: nullifier owned route

The owned `derive_nullifier_owned_with` callback takes its sixteen M31 input
limbs by value and translates without the shipped HRTB constraint. Aeneas
Charon: exit 0, 12.154 s, 612,744 KiB RSS; Aeneas: exit 0, 0.385 s,
71,808 KiB RSS. Both zero swaps. `BuilderNullifierExtracted` adapts imports
only; function bodies and generated resource settings are unchanged. It has
no external declarations. The callback trait is an explicit parameter.

`BuilderNullifierReference` proves total input packing, all eight key and
salt projections, exact execution against an arbitrary partial/stateful
owned callback, and success from that actual callback result. J9310/9311
compile the extraction and five lemmas, standard axioms only, zero swaps.
The final callback proof takes no HRTB, admission, canonicality, output
range, or preimage-equality premise. This is not yet a complete forest
semantic-admission theorem.

Four Kani/CBMC harnesses pass: raw-word preimage contract; owned preimage
versus that verified contract; shipped private callback versus owned
callback; shipped public function-item route versus the direct owned
wrapper. The latter two share one memoised oracle keyed by domain and
all sixteen limbs, with arbitrary answers including collisions. The table
is not reset between programs; both call counts equal two and the number
of distinct points equals one. No hash-function property is postulated.
`stub_verified` uses the raw-word contract; the M31 wrapper substitution
has its own relational verdict. Final command receipt `nullifier/kani-limbs`:
exit 0, 35.867 s, 5,675,292 KiB peak RSS, zero swaps, four successes.

Retained failures: initial verified M31-array stub cannot synthesize
Arbitrary; the raw-word replacement compiles but three array comparisons
hit the builtin memcmp byte-loop unwind assertion. Explicit sixteen/eight
limb comparisons replace those memcmps. The bound stays 18; no cap or
unwind-bound increase, dropped assertion, or unchanged retry is used.
The proof-only revisions leave every cfg-independent reference function
body byte-identical to the successful extraction input; the collector
checks the retained initial snapshot against the current source.

A fresh forest reference extraction replaces only the shipped nullifier
call by its owned reference in an isolated reference-source copy. Charon
passes (10.830 s, 618,380 KiB RSS), then Aeneas exits 2 (2.315 s,
463,360 KiB RSS) at incremental_merkle.rs:285–286,
RegionsHierarchy.ml:193: the borrowed validated-tree Result.map(into_inner)
call. It has passed the earlier nullifier lifetime frontier. The exact
source substitution is retained; this rejected forest output is not a
kernel certificate. All these attempts have zero swap.

The production registration is only the cfg(kani)/cfg(aeneas_ref) module
at the end of spend.rs. All three frozen ELFs have been rebuilt with the
current shipped crate sources and compare byte-for-byte (cmp exit 0) to
the retained frozen artifacts: dfc2a91a…, fb2fc048…, 121f3e29….
The excluded proof-only reference file has subsequent Kani-only revisions;
every production input matches the checkout. Receipts, source comparisons,
full log hashes/sizes, and exact commands: builder-cont7-host-evidence.json.


## Stages 3–4: runtime and execution

The shipped RuntimeJoin is not constructed. Its admission field needs
embedded RspendPlus, including append/carry and the D50 sentinel, from actual
successful-source execution. After the nullifier replacement the forest
caller reaches a separate borrowed capability boundary in the validated
incremental tree. A diagnostic-only explicit-match rewrite of Result.map
passes that point, then Aeneas fails in the validated append_one carry loop:
incremental_merkle.rs:189–193, InterpMatchCtxs.ml:230, visiting a shared borrow
retained in the validated capability. Charon 0 (9.484 s, 614,816 KiB RSS),
Aeneas 2 (2.252 s, 484,564 KiB RSS), zero swap. This diagnostic substitution
is not certified or shipped. The actual carry/frontier capability needs a
separate owned reference/callee proof; neither a larger cap nor another
unchanged compiler replay can supply it. That rejected output is not a
certificate. The remaining primitive Parts content joins are also not
proved; the now-closed Vec wrapper is removed from the remaining list.

`PrivacyR1FinalReleaseSource2` includes the new proof modules and preserves
all original binders and the complete freshness conclusion. Its runtime and
real/ideal execution joins remain explicit. There is no instantiated shipped
HonestProver on the actual successful compiler domain, and no concrete
source FSExperiments observation/randomness law connecting checker input,
P_chk/P_R1, pole/VR1, masks, retries, non-Rejected errors, publication,
serialization and reached-query history. The endpoint still quantifies over
an arbitrary source experiment. The inherited checked
BuilderExecutionBoundary.no_constant_mismatch_join demonstrates why builder
facts cannot imply that arbitrary-source execution join. No subtype carrying
RspendPlus, canonical-h substitution, fabricated runtime inhabitant or
execution premise with arbitrary bad events is introduced.

The exact binder diff is therefore empty, excluding the theorem name:
zero deleted premises, zero added premises, no claimed strict weakening.
The complete before/after signatures follow below.

## Resource and evidence audit

All new Lean sources are compiled one module per env-J attempt, before their
dependent bridge. No original release/privacy/quotient module is edited.
No unchanged full regression or frozen-manifest replay is claimed. All
final theorem/definition audits, source SHA, direct-import fingerprint,
source revision/dirty flag, wall, RSS and swap are retained.

The inherited launcher's shallow reservation glob missed nested user scopes.
J9308/9309 report only their own shallow aggregate check (24/26 GiB before
the 8 GiB job); their valid per-job cgroup receipts do not establish a
complete aggregate reservation guard. The task-owned launcher now scans
all populated cgroups recursively. Later jobs wait on that complete scan;
no other worker is stopped. Every job retains MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. Rust work is solver/proof compilation or
optimized SBF compilation, not an unoptimized arithmetic release gate.

The three rebuilt ELFs also pass cmp against the retained frozen artifacts.
Default: 32.528 s, 647,668 KiB; devnet: 2.790 s, 203,092 KiB; Pool: 29.186 s,
643,988 KiB; all exit 0 and zero swap. No shipped crate input changes after
this gate. Kani-only edits are confined to the excluded reference file.
The narrow extraction workspace has four stale, unused prover siblings;
all actual statement/core/copy inputs match. The isolated full ELF workspace
matches all production inputs in this checkout.

P6 evidence remains under the named Kani/CBMC, compiler/extraction and std
adapter trust boundary. No theorem asserts Kani soundness or promotes a
solver receipt into a kernel axiom. No binary, object, LLBC or key is
committed. No key cleanup, merge or push is performed.

## Verbatim endpoint signature audit

No source premise is discharged by the partial component theorem. Thus the
binder/conclusion diff, excluding the theorem name, is empty: deletion-only
with zero deletions, **not** a strict weakening. Both runtime and execution
joins remain. The new endpoint preserves the inherited freshness error and
strict <2^-100 conclusion. No stronger premise replaces an inherited one.
The audit script asserts complete binder and conclusion identity.

Before, verbatim:

```lean
theorem privacy_R1_release_source
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
theorem privacy_R1_release_source2
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
