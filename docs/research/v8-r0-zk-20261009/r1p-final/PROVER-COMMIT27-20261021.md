# Prover commitment part 27

Base `26b922be6`; branch `codex/cx-prover-commit27-20261021`.
Target not yet established. This report is updated at each verified stage.
The final job-specific Env J range 7636–7699, then 7700–7799, is used after
checking the shared receipts. No shipped or concurrent-owned file changes.

## Stage 1 — explicit CoinOracle state and product marginals

`ProverCommitCoinTape27` introduces a state-passing Digest32 interface returning
both digest and full updated state: cursor, optional recorded table and sticky
collision flag. `call_preserves` identifies source-order control with the
explicit-state reference under the D133 named ordered-map contract.
`sequence_preserves` lifts this equality to arbitrary finite adaptive call
trees, retaining the complete final state and ordered query/answer history.
`cursor_history` counts every call, including duplicate and exhausted reads.
The old pure generated dictionaries are not overwritten or silently given a
stateful meaning. This new interface is an owned formal reference, not yet an
Aeneas extraction of the complete caller cone.

`ProverCommitCursorMarginal27` transports both D134/D135 product marginals
through deterministic initialization and effectful adaptive evaluation.
`ProverCommitTranscriptTape27` binds the tape to the actual 115 stream-0
addresses of the existing product oracle. `stream_disjoint` and
`transcript_unchanged` prove stream-3 rejection packing leaves every transcript
coin unchanged. `product_coins` identifies the whole cursor-indexed tape,
including its zero fallback. `execution_law` retains final state and complete
history in the tested observation; it does not post-select on a final cursor.
No new randomness, freshness premise, or source-join trust item is introduced.

J7638 passes the three state/sequence audits (2.07 s, 4091608 KiB RSS);
J7640 passes three marginal audits (1.85 s, 4087260 KiB);
J7641 passes four concrete-tape audits (1.89 s, 4164988 KiB).
All exit 0, zero swap, standard axioms only. Receipts record exact modules,
source revisions/snapshots, dependency hashes and full axiom lines. J7636 and
J7637 are retained parse/instance failures; J7639 is a passing predecessor
whose unused rejection-coin accessor was removed before J7640.

The first combined Kani RefCell/reference gate timed out at 120 s. It is not
verification; a smaller fixed-input-length gate is in progress. Table operations
use the D133 approved contract projected to the current query key, rather
than another attempt to verify B-tree internals. Native cursor arithmetic is
checked only below usize::MAX; the Nat model still needs its bounded-caller
connection at the actual execution boundary.

## Still open

Re-extraction and source binding of the extended effectful caller interfaces;
concrete builder/checker/retry, commitment programming and serialization joins;
`shippedProverExperiment`, both complete WholeRunJoins and endpoint deletion.
The generic call-tree theorem does not assert that the unchanged generated
semantic/circle/control callers already implement this call tree.

## Stage 2 — actual extracted state-passing oracle

`harness/effect27.rs` is an owned state-passing CoinOracle reference with the
D133 recording callback. Charon and Aeneas extract its complete operation,
including returned state; no external extraction templates are used.
The first byte-comparison loop hit Aeneas `InterpBorrows.ml:2731`; an explicit
comparison replaced it. The monolithic 32-comparison proof hit Lean's default
heartbeat budget, so four eight-byte source helpers and named symbolic lemmas
replace it. No heartbeat, recursion or memory limit was increased.

`AspisR1CoinEffect27` contains the resulting actual generated API.
`ProverCommitExtractedCoin27` proves every byte-comparison helper and their
composition against complete array equality. J7652: exit 0, 15.35 s,
4247436 KiB RSS, swap 0, nine standard-only axioms audits.
`ProverCommitCoinCall27.call_exact` proves the complete generated call against
the reference effects, universally over finite vector length, cursor, table,
query and initial collision flag. It includes the actual wrapping machine
increment. `read_total` proves every read, including exhausted-tape zero fallback,
is defined. J7656: exit 0, 2.04 s, 4164120 KiB RSS, zero swap; both audits standard.

`extracted-call-v5` checks the literal shipped RefCell body against the exact
Rust reference used in the successful extraction: all three tape-length gates
(0/1/2) pass, arbitrary pre-overflow cursor, arbitrary full digest bytes,
recording on/off, prior answer and collision flag. Exit 0, 20.571 s,
1586016 KiB RSS, zero swap. It uses the separately verified universal full-byte
comparison contract (`different-v1`: exit 0, 1.988 s, 210496 KiB, zero swap).
The map implementation is a projection of the D133 trusted map contract to the
current key; these are bounded library/control gates, not verification of all
native vector lengths or B-tree internals. The universal extracted equation
is a separate Lean theorem. Earlier timeouts/unwind/compile diagnostics are
retained and excluded. The accepted gate records prelaunch reservations.

Actual owned effectful caller extraction has also succeeded for the literal
semantic/circle three-read helper and suffix block/query-materialization
skeletons (`callers27.rs`); their source equations and whole-source composition
are the next stage. The policy, retry, native trace and serialization boundaries
are not discharged by this interface extraction.

## Stage 3 — generated call-sequence and caller effects

`ProverCommitCoinSequence27.generated_sequence` is an induction over the
**actual extracted** CoinOracle operation, for arbitrary finite adaptive
programs. It preserves value, final machine state and ordered input/digest
history with no successful-call hypothesis; machine wrapping remains exact.
`step_view` identifies the full machine state with the Nat reference below
wrap, with an explicit arithmetic room condition rather than an execution
join hypothesis. J7662 passes both audits (exit 0, 1.92 s, 4174608 KiB, swap 0).

`ProverCommitMachineMarginal27.initialMachine` is the actual finite 115-entry
machine vector, decoded from the existing product table's stream-0 addresses,
with cursor zero and explicit recording initialization. `initial_product`
identifies it with the model's retained table projection. The source and model
marginals now apply to the actual extracted interpreter, retaining the complete
result, cursor, recording/collision effects and ordered history. J7668 passes
all three audits (exit 0, 1.89 s, 4171904 KiB, zero swap).

`AspisR1EffectCallers27` extracts the literal three-read helper shared by
semantic/circle sampling, the suffix absorb/block, and the full eager query
materialization. The owned trait changes `&self` into `&mut self`; the extracted
trait returns `(digest, updated hash state)` at every call. Original pure
owners remain unchanged. The generated one-variant error discriminant is given
an explicit local name to avoid the pinned generator's global-name collision;
the raw file is retained. J7664/J7665 compile the ported types/functions.

`ProverCommitEffectCallers27.semantic_call` and `block_call` identify the
extracted bodies with explicit adaptive three-call programs, retaining final
hash state. Mismatched semantic rows return without reads. The history-length
lemmas establish zero/three reads and exactly three suffix reads.
`dictionary_exact` identifies the concrete source dictionary with the concrete
expected-state step. `query_effects` transports it through the complete eager
query materialization, retaining all sixteen reads, the initial absorb, all
errors and returned hash state. J7672 passes six audits (exit 0, 1.93 s,
4163060 KiB, zero swap); standard axioms only.

`source-binding.json` checks byte-for-byte copies of the native CoinOracle,
semantic helper (visibility change only), suffix absorb/block and exact query
prefix through all sixteen reads. This is source binding of call skeletons,
not a claim that arbitrary decoder/validator policies implement the whole walk.
The concrete old decoder/checker policies still need installation into the
new effectful full continuation, including retry, trace and serialization.
J7661 was preflight-only (missing predecessor object); it launched no compiler.
All other failed predecessors and exact snapshots are retained.

## Concrete whole-caller boundary

J7673 is an intentionally excluded installation probe. The complete retained
`AspisR1SimControl21.transcript.control21.Transcript.queries` still accepts its
old pure `Digest32` dictionary. Installing the new concrete digest fails with:

```text
has type
  Machine → Slice (Slice U8) → Result (Bytes32 × Machine)
but is expected to have type
  Machine → Slice (Slice U8) → Result Bytes32
```

The new effectful *call skeletons* are verified above, but do not replace the
entire semantic/circle/control policy continuations and full walk owner. In
particular, the new query skeleton stops before concrete scanner selection,
native trace publication and rho. The old continuation cannot consume the
updated hash state without being ported; projecting away that state would
reintroduce the disproved D136 stateless interpretation. The exact probe,
type inventory, source snapshot, error and resource receipt are retained.
No successful theorem imports this diagnostic; its failed source is outside
the Lean source tree.

This obstructs direct whole-caller installation and therefore stage (3).
It is an interface-composition obstruction, not a privacy counterexample or
a new impossibility theorem. Full continuation extraction/porting is the next
concrete deliverable. `shippedProverExperiment`, both real/ideal WholeRunJoins
and endpoint specialization remain unconstructed. No source-refinement
assumption has been hidden inside TrustedStd, a callback, P6 or P7.

## Verbatim endpoint before/after

The whole endpoint module is byte-identical to base `26b922be6`. Both copies
below use unchanged surrounding parameters and local notations. The empty
`endpoint-deletion.diff` removes zero premises. This is not a completed
deletion-only discharge; no quantifier, carrier, bad event or conclusion changed.

Before:

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After:

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

## Native-length gate refinement and final verification

The direct native 115-word RefCell/reference gate (`native115-v2`) timed out
at 90 s; its predecessor `native115-v1` failed only the 115-element arbitrary
array construction unwind. Neither is verification. The first shared-input
whole-word read cell (`read115-v1`) also timed out at 90 s. The replacement
`read-address115-v1` proves the exact library address fact instead: for an
arbitrary 115-word vector and arbitrary cursor, `get` either returns the same
immutable cell as indexed access, or returns none exactly beyond the end.
Exit 0, 8.436 s, 798492 KiB RSS, zero swap, unwinding assertions enabled.
This avoids muxing/copying all 32 bytes twice. It complements the passing
small-vector RefCell/effect gates and universal extracted `read_total` lemma;
it is not reported as a successful monolithic 115-word RefCell gate.

J7674 passes `R1Z/ProverCommit27Audit.lean`: exit 0, 1.77 s,
4199196 KiB peak RSS, swap 0, source revision `f09769794` plus the exact
additive audit-source SHA/dependency fingerprint. All 34 complete audit lines
(32 new facts and both retained endpoints) use only the accepted standard
axioms, or fewer. Exact target, exit, wall, RSS, swaps, revisions, snapshots,
transitive dependency hashes and full axiom/error lines are in `lean/`.
The audit coherently imports the final changed dependency closure; it does
not assert a complete shipped-game execution law.

All Lean and Rust host jobs used the specified 6G/8G/no-swap/64-task scopes.
No recursion/heartbeat limit was raised. Extraction used optimized Cargo;
Kani time was in CBMC, with the requested RUSTFLAGS. Timeout parent RSS can
omit killed descendants; the retained cgroup peak is the aggregate metric.
No unchanged full regression or frozen manifest was replayed: whole-source
release preflight is not green. Earlier D129 artifact evidence is reused.
No tracked file under `crates/` or `programs/` changed, so the shipped-file ELF
rebuild rule is not triggered. No concurrent-owned source, wallet, key,
binary/object/archive, or local target directory is changed or committed.
No push. Next Env J candidate is 7675, subject to the shared receipt check.

The requested deployed target is **not yet established**. The next deliverable
is the complete effectful walk/policy continuation, including replay reset,
query selection, native trace, retries, commitment programming and ordered
serialization, followed by the concrete real/ideal WholeRunJoins. The endpoint
above retains `RustProverRefinement` explicitly; zero premises were removed.
