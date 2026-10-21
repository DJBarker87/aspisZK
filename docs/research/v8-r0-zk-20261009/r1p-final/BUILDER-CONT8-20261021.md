# Builder continuation 8

Branch `codex/cx-builder-ref8-20261021`, base `71b7f0db3`.

## Stage 1: owned validated-tree carry

Partial closure. The owned reference copies the authenticated empty table
and inner tree and consumes its capability on append. The shipped append
body is unchanged. The approved fallback is a projected one-step P6 check
plus an extracted-loop invariant; no whole-append Kani verdict is claimed.

## Admission, Parts content, runtime and execution

Not fully discharged. The extraction advances to a new raw mutable-pointer
destructor blocker. The new primitive writer identities and withdrawal aux
content are proved, but no complete runtime/execution join follows. No source
endpoint premise is claimed removed.

## Frozen program gate

All three optimized SBF rebuilds pass with the final cfg-only registration:

| Program | SHA-256 | wall | peak RSS KiB | swap |
|---|---|---:|---:|---:|
| default | `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` | 29.097 s | 446248 | 0 |
| devnet | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | 3.077 s | 203576 | 0 |
| Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 32.523 s | 430856 | 0 |

Each has exit 0 and `cmp` exit 0 against the retained frozen artifact.
All actual production inputs in the isolated full build workspace match
this checkout. The inherited cfg-only nullifier reference has older Kani
harness metadata, which does not enter any production build. The narrow
statement extraction workspace also has stale, unused prover siblings and
a narrowed manifest, as inherited from continuation 7; no source identity
claim is made for those unused siblings. Exact pins and receipts are in
`builder-cont8-host-evidence.json`. No binaries are committed.

## Retained unsuccessful experiments

- `tree/kani-full`: compile-time path error; corrected relative path.
- `tree/kani-path`: full-loop symbolic array replay stopped at the
  MemoryHigh review, 195.208 s, 6,393,588 KiB RSS, zero swap. Kani reports
  CBMC status 15, not a solver verdict. No larger-cap retry.
- `tree/kani-fixed01`: fixed trailing-one count with full array replay,
  timeout at 240 s; no owned-tree verdict. Its short selector incidentally
  also selected the inherited glue-tree case 01 (400 checks pass). That
  inherited verdict is not new evidence and does not certify this append.
  GNU time's timeout-parent RSS is incomplete; no true job peak is claimed.
- Initial method and module Charon selectors returned empty/no-function
  extractions. They are rejected even though both tools exited 0. The
  free-function entry selects the actual append loop and result wrapper.
- `tree/aeneas-entry`: nonempty append extraction succeeds (1.979 s,
  132,352 KiB RSS, zero swap), but contains nine unsupported std/opaque
  declarations. It is a diagnostic artifact, not an accepted certificate.
  The isolated owned callback carry extraction is the next narrower target.

## Stage 3 component: primitive path and auxiliary writers

`BuilderPrimitiveWriters` identifies every actual aggregate-extraction
path/aux writer with the previously checked copy writer, including the
complete Result behaviour. The proof uses symbolic suffix induction at
bounds 30, 3, 8 and 24; no trace cell table is reduced. `occRecord` is an
explicit five-field map between the extraction-specific occupancy types.
The twelve theorems cover m31_sub, the complete value writer and both loops,
occupancy row and its loop, auxiliary block, path row base, path level and
its loop, and the complete path block and its loop.

Env J 9324 passes: exit 0, wall 2.59 s, peak RSS 3,746,796 KiB,
zero swaps, all twelve audits use only propext/Classical.choice/Quot.sound.
9321–9323 are rejected elaborations (header parsing, scalar increment lemma
and a local converter name collision), retained with their corrected source
fingerprints. No failed theorem or `sorryAx` result is accepted. This
closes the duplicated primitive path/aux writer identity, **not yet** the
Parts arguments: source tree/chunk/digest/occupancy-inverse correspondence
still has to feed those same checked writers. No Content or endpoint
premise is silently removed.

## Stage 1 result: projected carry step and symbolic loop

`carry_step_owned` accepts the frontier-node and empty-node values by value.
The shipped loop's two array reads project to these arbitrary values. The
Kani harness calls the actual `pool_v1_tree_parent` function item under a
shared arbitrary oracle, checks both full eight-limb inputs and call count,
and compares every returned carry/cleared-node limb and the level increment.
It does not assume collision-freedom, canonical words or a digest range.
The source-slice substitution is explicit in `builder-cont8-step-audit.json`:
this is a projected one-iteration check, not a whole append_one verdict.
Array reads/updates and frame preservation are separate Lean facts.

`projected/kani-step`: exit 0, 16.721 s wall, 929,756 KiB peak RSS,
zero swap, 368 checks (three unreachable), all unwinding assertions enabled.
The final reference file is byte-identical to that successful workspace.
The whole-array one-step predecessor also timed out at 240 s, without a
verdict; the successful replacement removes array bookkeeping from CBMC
and supplies it with checked symbolic array laws instead. No unwind bound
is raised and no assertion is dropped from the narrower stated contract.

The generic `carry_owned_with` has an owned, partial/stateful parent callback.
Its actual extraction has no external declarations. `BuilderTreeCarry`
proves the exact carry transition, stop bound/guard, clearing of precisely
[start,stop), and preservation of all other frontier cells by suffix
induction on 20-level. `BuilderTreeStep` proves the extracted callback step
and complete array frame law. The extraction adaptation changes imports
and uses the existing proved shift64 adapter for the backend's usize/U32
shift-count mismatch. The standalone step declaration is selected from the
second extraction without editing its function body. Exact adaptation and
source pins: `builder-cont8-adaptation-audit.json`.

These are reference-component theorems under the named P6 compiler/Kani
boundary. No Kani soundness axiom, full append receipt/root reconstruction
certificate, or shipped runtime inhabitant is manufactured.

## Stage 2 obstruction: trace zeroization destructor

A fresh forest extraction substitutes the owned validated tree in the two
plain append constructors and from_parts wrapper, in an isolated reference
source copy. The constructor validates the same raw inner tree and returns
its owned table; the append reference retains the original carry, root and
receipt construction. The earlier nullifier P6 substitution and opaque
records/lazy external declarations are retained and explicitly recorded.
This is an exploratory extraction with named boundaries, not an accepted
whole-source certificate.

Charon passes: exit 0, 11.558 s, 615,788 KiB RSS, zero swap.
Aeneas now passes the validated-tree borrow frontier and stops at:

> Unsupported operation: &raw mut (*value)
> state_only_trace.rs:90:51–90:56, InterpExpressions.ml:1468

This is `StateOnlyTraceFoundation::drop`, which performs the intentional
volatile wipe of the unmasked witness. It is not an allocator rewrite or
an empty destructor. Deleting it or silently modelling it as a no-op would
need a separately justified observation/heap-lifetime boundary; none is
introduced here. The rejected output is not compiled or counted as an
admission certificate. No source-limit/cap increase or unchanged replay is
used. Complete semantic admission (including append/root and sentinel),
and therefore RuntimeJoin.admission, remain open.

## Stage 3 result: actual withdrawal auxiliary Parts content

`BuilderPrimitiveArguments` maps the actual RW/RP fields to RustWitness and
RustPublic. It proves the actual input occupancy computation and all five
record fields, identifies the two zero digests, and proves the actual
withdrawal auxiliary writer call equals auxR for arbitrary raw words.
`parts_aux_content_withdrawal` derives the exact inherited Content.aux
field from successful actual parts execution and p.transfer=false. It
assumes neither auxiliary-array equality nor semantic admission.

Still required: source chunk/digest/tree argument correspondence for path
and blocks; transfer change-digest/inverse arguments for aux. The generic
path/aux writer identities from stage 3 remove duplication of those writers,
but are not substitutes for their missing arguments. Full primitive
Content is not claimed.

## Stages 4–5: runtime and checker/retry remain explicit

The shipped `RustRuntimeJoin` is not inhabited: its admission and complete
raw_trace_eq depend on the unresolved items above. The endpoint continues
to quantify over arbitrary h; replacing it by a canonical h or assuming
RspendPlus in an instance subtype would not prove the requested source join.

The actual checker/retry experiment and randomness/observation coupling are
also not constructed. The inherited checked
BuilderExecutionBoundary.no_constant_mismatch_join remains a direct
obstruction to deriving that arbitrary-source execution join from builder
facts. P_chk/P_R1 identity, pole/VR1, masks, retry/non-Rejected errors,
publication, serialization and reached-query observation still require a
concrete source law. No arbitrary bad event or fabricated ModelExecutionJoin
is substituted. Source3 preserves both fixed-event joins, the full freshness
error and strict <2^-100 conclusion; its signature diff is audited below.

## Evidence and resource notes

All task builds use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64; Rust commands use four cargo jobs and the required linker flag.
Recursive reservation guards wait for the 55 GiB allowance. Shared-host
reservation scans are observations, not an atomic reservation protocol with
other workers; waits observed higher aggregate reservations and did not
stop any other worker. No wallet operation or key cleanup is performed; inherited build keys remain retained.

Rust receipts identify the starting revision plus the uncommitted source
pins retained with each extraction/workspace. The final source/hash audit
binds the accepted projected reference to this checkout. Timeout-parent
RSS values in the failed Kani experiments are incomplete and are not used as
true job peaks. The cancelled literal-only experiment raced with launch;
its task-owned solver was explicitly stopped with no verdict, and the
retained cancellation records describe both events.

Two concurrent Lean submissions collided at attempt 9333. Both records are
explicitly invalidated and excluded from accepted evidence. The runner now
reserves attempt IDs under a task-local allocation lock and releases it
before calling run-joint (the launcher is never wrapped in another flock).
The affected modules receive actual source revisions and fresh focused
attempts. No source/receipt mismatch is accepted as a theorem certificate.

All original release/privacy/quotient modules are untouched. Only the
five-line cfg-only registration at the end of incremental_merkle.rs changes
a shipped file; the three ELF rebuilds above cover it. Subsequent reference
proof edits remain excluded from production. No binary, object, LLBC or key
is committed; no push, merge, full manifest replay or unchanged runtime
suite is performed.

## Final focused verification

The accepted final set is seven current modules and 26 named theorem audits.
All sources and dependency-object fingerprints match their focused receipts;
all accepted axioms are a subset of propext, Classical.choice and Quot.sound,
and all final Lean attempts have zero swaps. The two invalid attempt-9333
records are excluded. Exact evidence and tool/environment pins are in
`builder-cont8-final-audit.json`; all failed and corrected elaborations remain
in `builder-cont8-attempts.jsonl`.

| Module | attempt | exit | wall | peak RSS KiB |
|---|---:|---:|---:|---:|
| `R1Z.BuilderPrimitiveWriters` | 9324 | 0 | 0:02.59 | 3746796 |
| `R1Z.BuilderPrimitiveArguments` | 9335 | 0 | 0:01.94 | 3737700 |
| `R1Z.BuilderTreeCarryExtracted` | 9326 | 0 | 0:01.37 | 2535176 |
| `R1Z.BuilderTreeCarry` | 9334 | 0 | 0:02.34 | 4014536 |
| `R1Z.BuilderTreeStepExtracted` | 9332 | 0 | 0:01.21 | 2524212 |
| `R1Z.BuilderTreeStep` | 9336 | 0 | 0:01.74 | 4005560 |
| `R1Z.PrivacyR1FinalReleaseSource3` | 9337 | 0 | 0:03.34 | 4113044 |

The endpoint is checked against Source2 verbatim below. It removes no
premise; no strict weakening or completed source release is claimed. The
current shipped-file change is covered by all three successful frozen ELF
hash and byte comparisons. Every completed component has its own commit.
The new outstanding extraction target is the trace zeroization destructor;
full admission, remaining Parts content, concrete runtime and execution joins
remain open. No task-owned host build is intentionally left running.

## Verbatim endpoint signature audit

No complete runtime or execution join was discharged. The binder/conclusion
diff is empty, excluding the theorem name: deletion-only with zero deletions,
not a strict weakening. No new or stronger premise is introduced. The error,
freshness term and strict <2^-100 conclusion are byte-identical.

Before, verbatim:

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

After, verbatim:

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
