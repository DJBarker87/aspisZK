# Prover commitment part 19 — seed event and shipped experiment

Base `28776b162`; branch `codex/cx-prover-commit19-20261021`.

**Target not yet established.** The seed-augmented deployed bound and bounded
joint-history coupling are proved. Full shipped execution remains blocked by
the source translation and transport obligations recorded below. Concurrent-worker modules SourceIdentification,
RustRuntimeJoin and PrivacyR1FinalRelease are untouched.

## Scope and mathematical accounting

D127 authorizes a seed-guess exception and its explicit privacy loss. The
constructed model has no simulator-seed coordinate; the new event must use
an independent retained seed, rather than assuming that an existing model
coordinate is independent of its own observable history. The global event
must be counted once, outside the eight-attempt union.

## Evidence

Focused Lean checks run on the NUC, one at a time, in env J using unused
attempts 8675–8799. Each scope has MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0 and TasksMax=64. Exact snapshots and JSONL receipts are stored
in `docs/research/100bit-spend-path-20261013/evidence/prover-commit19-20261021/`.
No full frozen-manifest replay is claimed until the focused dependency cone
is green. Source revision, exit, wall time, peak RSS, swaps, dependency hashes
and full axioms lines are retained in the per-attempt receipts.

## Stage 1 — seed accounting and premise transport

`ProverCommitSeedEvent19.seedPoint` tests the exact source domain and 32-byte
seed prefix. It deliberately also charges malformed suffixes in that namespace.
`source_point` proves containment of every source coin address, for every
attempt, stream and counter. `seedPoint_unique` proves that any query names
at most one seed. `seed_mass` proves the resulting q/2^256 upper bound for a
list depending arbitrarily on all model coins and adaptive answers, independent
of the separately retained seed. No seed carrier is enumerated.

`augmented old queries i (m,seed)` is
`old i m ∨ (i = 0 ∧ seedGuess (queries m) seed)`.
`old_contained` and `union_mass` prove containment and a single global charge,
not eight charges. `ProverCommitSeedJoin19.of_old` constructs an actual product
extension of the old coupling; the runtime/model observations do not change.
This proves implication of old certificates to augmented certificates. Proper
inclusion for each adversary is not asserted (an observer making no queries
has no seed-guess event).

`ProverCommitObserverQueries19` exposes the exact adversary-only `runLog`
suffixes in real and ideal games, including failure exits; both lengths are
at most W.qmax. The query functions retain the original shared table and
programmed fallback. They do not replace adaptive queries by fixed addresses.

Accepted focused checks: J8681 seed events (exit 0, 2.12 s, 4,042,740 KiB),
J8683 generic join/numerics (exit 0, 2.45 s, 4,060,364 KiB), J8685 query caps
(exit 0, 2.05 s, 4,037,844 KiB). All swaps 0; all printed axioms are subsets
of `[propext, Classical.choice, Quot.sound]`. Revisions are `28776b162` plus
exact snapshot hashes. Earlier attempts are retained and excluded: the errors
were local rewrite/decider/instance normalization, repaired without changing
resource limits. Existing shared objects were not overwritten in this stage.

The numerical proof is symbolic: at q ≤ 2^64, one seed charge is at most
2^-192; two coupling sides add at most 2^-191. The old conservative upper
bound plus these terms is at most 8·2^-109 = 2^-106 < 2^-100. No old loss is
removed or hidden. Connecting this result to the deployed signature is the
next stage; concrete shipped execution and full simulator history remain open.

## Stage 2 — deployed endpoint with explicit seed events

`RustProverRefinement` now uses `ProverCommitSeedJoin19.RunJoin`: its model
randomness is the existing model randomness times an independent uniform
32-byte seed. Its agreement includes the whole ROMView and observer decision
outside `augmented oldBad fixedQueries`. The query suffix functions fix the
ordered source observer and include abort exits. `LegacyRustProverRefinement`
is the verbatim old premise; `legacy_refinement_implies` proves its implication
to the new premise with unchanged observations, using product extension.
No source refinement has been assumed or discharged by this transport.

The privacy error and its upper bound now explicitly add
`2 * ProverCommitSeedEvent19.budget (2^64)` = 2^-191: one global seed charge
for each of the real and ideal coupling comparisons. Each charge covers the
entire eight-attempt run. Keeping the real-side allowance too is conservative;
neither charge is multiplied by eight. All old error terms are retained.
The result remains strictly below 2^-100.

J8688 passes: exit 0, 12.70 s, peak RSS 4,203,096 KiB, swaps 0, revision
`b1978fda4` plus exact source snapshot hash; standard axioms only. J8686–8687
are excluded local annotation errors. The shared deployed source/object was
snapshotted under the part-19 host workspace before replacement. New consumers
must use this new dependency; this is not evidence for an unchanged old olean.
No concurrent-owner module is edited or replayed.

The exact before/after full files are `endpoint-before.lean.txt` and
`endpoint-after.lean.txt`, and the complete change is `endpoint.diff` in this
pass's evidence directory. The following are the verbatim new top statements.

```lean
theorem legacy_refinement_implies
    (old : LegacyRustProverRefinement template outputs x rust observer_program) :
    RustProverRefinement template outputs x rust observer_program

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) < 1 / 2^100
```

## Stage 3 — joint histories rather than marginal coins

`ProverCommitJointHistory19.swapCoordinates` is an actual equivalence: it
exchanges the independent coin vector with the corresponding entries of the
single shared oracle table. `seededCoupling` retains the seed and proves both
whole marginal laws exactly. `replace_at` recovers every source coin from the
same replaced table; `replace_off` retains all other oracle answers.

`runLog_agrees` inducts over the adaptive program, preserving the complete
ordered address/answer history, repeated queries and early exits.
`byte_history_agrees` specializes this to the actual 65-byte simulator coin
frames, all eight attempts, all four streams and any bounded counter schedule.
`programmed_history_agrees` additionally retains an arbitrary coin-dependent
programming table before the shared-oracle fallback. `joint_observation`
retains an arbitrary public view of all the coins, so deterministic bounded
retry, acceptance, error and serialization projections can be included in it.

`componentJoin` constructs the complete component RunJoin with only the
single seed exception; its pointwise lookup obligation is discharged for the
source byte table by `byte_oracle_agrees`. This is the joint law missing in
part 18. It is not yet a source identification of the full simulator: the
bounded coordinate schedule, actual view calculation and uncapped source
nonzero loop still need their source certificates. No RustProverRefinement
premise is removed, and no shippedProverExperiment is claimed.

J8694 passes the final enhanced module: exit 0, wall 2.27 s, peak RSS
4,043,648 KiB, swaps 0, revision `59790da74` plus exact source hash; all
printed axioms standard (exchange has none). J8689/J8690 checked earlier
versions; J8691–8693 exposed local elaboration issues, retained and excluded.
The replacement avoids reducing concrete finite address/coin enumerations;
no recursion or heartbeat limit was changed. These are focused component
checks, not a coherent frozen release replay.

Verbatim joint equality and coupling statements follow; the full RunJoin
constructor is in the source snapshot.

```lean
def seededCoupling {S : Type} [Fintype S] [Nonempty S]
    [Fintype A] [Fintype I] [Fintype U] [Nonempty U]
    (key : S → I → A) (injective : ∀ seed, Function.Injective (key seed)) :
    Coupling (S × (A → U)) (((I → U) × (A → U)) × S)

theorem joint_observation {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) [Fintype (RomFiniteBin.Address bound)] (fits : 65 ≤ bound)
    {V : Type} (view : (ProverCommitSimulatorOracle18.Index count → OracleAnswer) → V)
    (program : V → OProg) (fuel : Nat)
    (seed : OracleAnswer) (coins : ProverCommitSimulatorOracle18.Index count → OracleAnswer)
    (table : RomFiniteBin.Address bound → OracleAnswer)
    (fresh : ¬ seedGuess (runLog (program (view coins)) (RomFiniteBin.lookup bound table) fuel) seed) :
    let key := ProverCommitSimulatorOracle18.key (count := count) bound fits seed
    let hinj := ProverCommitSimulatorOracle18.key_injective room bound fits seed
    let sourceTable := replaceTable key hinj coins table
    let sourceCoins := fun i => sourceTable (key i)
    (view sourceCoins, runLog (program (view sourceCoins))
      (RomFiniteBin.lookup bound sourceTable) fuel) =
    (view coins, runLog (program (view coins)) (RomFiniteBin.lookup bound table) fuel)

theorem programmed_history_agrees {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) [Fintype (RomFiniteBin.Address bound)] (fits : 65 ≤ bound)
    (seed : OracleAnswer) (coins : ProverCommitSimulatorOracle18.Index count → OracleAnswer)
    (table : RomFiniteBin.Address bound → OracleAnswer) (entries : List Entry)
    (program : OProg) (fuel : Nat)
    (fresh : ¬ seedGuess (runLog program
      (programmedOracle entries (RomFiniteBin.lookup bound table)) fuel) seed) :
    runLog program (programmedOracle entries (RomFiniteBin.lookup bound (replaceTable
      (ProverCommitSimulatorOracle18.key (count := count) bound fits seed)
      (ProverCommitSimulatorOracle18.key_injective room bound fits seed) coins table))) fuel =
      runLog program (programmedOracle entries (RomFiniteBin.lookup bound table)) fuel

```

## Stage 4 — per-draw entropy rejection and sixteen-step induction

The former 600-second entropy exhaustion gate is replaced by three one-draw
checks. `make-entropy-step.py` extracts the verbatim body of the production
`generate` loop, retaining getrandom, Zeroizing buffers, all three source
slices and the source conjunction. It changes only successful return framing
from `Ok(Self {...})` to `Ok(Some(Self {...}))` and appends `Ok(None)` for a
rejected draw. The exact source/body hashes and these two literal replacements
are recorded in `entropy-step-binding.json`. The original generator and its
sixteen-iteration loop are not changed.

Each Kani target supplies an arbitrary 96-byte candidate through the stubbed
OS boundary, constrains one complete 32-byte block to zero, and proves exactly
one call and `Ok(None)`. The other two blocks remain arbitrary, including
additional zeros. The proofs execute source slicing, validity checks and drop
code, with unwinding assertions enabled. They do not prove an OS law.

| Check | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| reject_block_0 / entropy-reject-block0-v2 | 0 | 17.252 | 918988 | 0 |
| reject_block_1 / entropy-reject-block1-v1 | 0 | 18.795 | 919252 | 0 |
| reject_block_2 / entropy-reject-block2-v1 | 0 | 21.155 | 919340 | 0 |

Block0-v1 is an excluded compilation error: the copied `Self` body needed
its enclosing impl. V2 restores that context; it does not weaken the gate.
`#print axioms`: N/A for these Kani jobs. All use the specified four-job,
6G/8G/no-swap/64-task scopes and linker flag; time is in compilation and
bounded symbolic byte/control checking, not debug arithmetic execution.

`ProverCommitEntropyStep19.rejected_prefix` proves the loop induction for
arbitrary different rejected draws and arbitrary retained states.
`sixteen_rejected` uses the per-block decode fact at each draw and returns
`RepeatedZeroBlock` with state exactly `states 16`. This closes the mathematical
and source-slice replacement of the old all-zero exhaustion check under the
named P6 source-body/control-flow boundary; it does not claim a new whole-run
Rust refinement or erase successful/OS-error cases from the experiment.
The already accepted part-18 first-success and OS-failure gates are reused.

J8696 passes: exit 0, 1.80 s, peak RSS 3,491,816 KiB, swaps 0, revision
`5c82dc920` plus source SHA-256; all four axioms audits standard. J8695 is an
excluded local Nat-zero normalization error. Verbatim final theorem:

```lean
theorem sixteen_rejected {State OsError : Type}
    (next : State → Except OsError Candidate × State) (states : Nat → State)
    (draws : Nat → Candidate) (blocks : Nat → Fin 3)
    (drawn : ∀ j < 16, next (states j) = (.ok (draws j),states (j+1)))
    (invalid : ∀ j < 16, draws j (blocks j) = 0) :
    generate next (states 0) = (.error .repeatedZero,states 16)
```

## Stage 5 — per-function simulator extraction and owned references

The full part-18 extraction is not retried unchanged. Splitting the actual
`sim::concat` root yields LLBC with `has_errors=false`, but Aeneas rejects
its borrowed iterator with “Nested borrows are not supported yet” at source
lines 89:4–89:44 (exit 2). The owned indexed reference avoids a live iterator
borrow across recursion. Its final extraction also has `has_errors=false`,
and Charon/Aeneas both succeed. No external function template is required.

`AspisR1SimulatorConcat19` is promoted verbatim except for narrowing the
root Aeneas import to the cached Std/RustAttributes imports. The generated
resource options are unchanged. `ProverCommitSimulatorConcat19.extracted_finite`
proves the full finite recursion for every admitted index/count pair, retaining
index, clone and append failures/divergence. The source comparison Kani check
passes for three arbitrary slices, each of length 0–4 (including empty slices):
110.011 s, peak RSS 4,442,628 KiB, exit 0, swaps 0. This is explicitly a bounded
source check, not universal borrowed-Vec/List transport.

The programming-table reference retains overwrite behavior, the sticky
collision flag and arbitrary 32-byte old/new answers. Its indexed owned
extraction has no external function template. `ProverCommitSimulatorInsert19`
proves its entire finite recursion, including append-at-end, overwrite,
conflicts, errors and divergence. Source BTreeMap/RefCell-to-Vec transport is
not inferred from that theorem. The broader one-existing-entry Kani gate was
stopped for proof-shape review; a narrower overwrite-only gate is separate.

The first recursive-pop versions of both references lower to external
`Vec.pop` templates. Those are excluded and never promoted: substituting
the generated axioms would violate the proof rules. The indexed replacements
remove that external boundary. Concat-owned-v2 is an excluded whole-crate
compile failure during invalid entropy instrumentation; v3 follows the
source fix and is hash-pinned independently.

| Accepted extraction | Charon wall s / RSS KiB | Aeneas wall s / RSS KiB |
|---|---:|---:|
| concat-owned-v3 | 34.591 / 578564 | 0.337 / 61600 |
| insert-owned-v2 | 30.606 / 577236 | 0.332 / 66000 |

All four exit 0 with swaps 0, under 6G/8G/no-swap/64-task scopes. Charon uses
`--release`, four jobs and the specified linker flag; time is in optimized
compilation/translation. LLBC bytes and binaries stay on the host; only hashes
and sizes are committed. Raw Lean text and exact import-only promotion
manifests are retained. `#print axioms`: N/A for translation; promoted source
and new finite-schedule theorems are separately checked below.

J8697/J8698 compile concat Types/Funs; J8699 audits its two new theorems and
the extracted function (exit 0, 1.42 s, 2,536,200 KiB). J8700/J8701 compile
insert Types/Funs; J8702 audits its two new theorems and the extracted function
(exit 0, 1.49 s, 2,541,136 KiB). All swaps 0 and accepted axioms standard;
exact revision/hash/dependency receipts are in the evidence directory.

### Remaining simulator extraction obstruction

Splitting the actual `walk` root with named opaque wire/transcript boundaries
produces valid LLBC (exit 0, 32.889 s, 576760 KiB), but Aeneas fails its loop
context match (exit 2, 0.721 s, 104016 KiB). An owned recursive reference for
its 25 semantic rows is then tried, retaining the advanced transcript and
semantic errors. With an opaque wire callee it translates (31.274 s Charon,
0.344 s Aeneas), but the generated files still require external transcript
state/error/method and map_err declarations. This result is excluded from
Lean promotion and supplies no source certificate.

Closing that owned row root's dependency cone, with no opaque wire module,
still gives `has_errors=false` (Charon exit 0, 36.113 s, 574640 KiB), but Aeneas
fails with an uncaught `Not_found` from
`InterpReduceCollapse.collapse_ctx_following_sequence` during a callee loop
context collapse (exit 2, 0.642 s, 84128 KiB). The direct generic semantic-method
root also exits 101 without an LLBC; its complete compiler stderr is retained,
and no mathematical conclusion is drawn from that failure. No unchanged or
higher-cap retry is performed.

This is the demonstrated remaining translation obstruction after the requested
function split and owned-reference attempt. A successful opaque outer driver
is not a full simulator extraction. Next: isolate the failing transcript/parser
callee loop, provide its owned source reference and exact source equality,
then link rows 25–32, programming/serialization traversal and error/retry
assembly. The uncapped nonzero loop and the full bounded-schedule/history
adapter still require source certificates. `shippedProverExperiment` is not
constructed; neither shipped WholeRunJoin is claimed, and the revised
RustProverRefinement remains explicit.

### Strictness and actual source changes

J8703 additionally proves `proper_at` and `strict_event_witness` (exit 0,
1.80 s, 4,034,544 KiB, swaps 0, standard axioms). The latter exhibits a genuine
source-frame query where the augmented event is true and the old empty event
is false. Together with `old_contained` and the actual
`legacy_refinement_implies`, this documents containment, proper event
extension and premise implication separately. Proper inclusion for every
fixed observer is false for a zero-query observer and is not claimed.

Only a `cfg(kani)` / `cfg(aeneas_ref)` reference module is appended to sim.rs.
Production source prefixes match `28776b162` byte for byte, including the
unchanged real entropy generator. This changes source hashes and proof
artifacts, but introduces no production configuration behavior change.
No SBF/ELF rebuild or new byte-equivalence result is claimed; historical
artifact evidence is not attributed to a new source build.

Verbatim source diff and the pre-seed endpoint statement follow.

```diff
diff --git a/crates/aspis-r1-cost-probe/src/sim.rs b/crates/aspis-r1-cost-probe/src/sim.rs
index 13110b794..432db2553 100644
--- a/crates/aspis-r1-cost-probe/src/sim.rs
+++ b/crates/aspis-r1-cost-probe/src/sim.rs
@@ -520,0 +521,43 @@ mod tests;
+
+// Proof-only owned references. Not enabled in any production configuration.
+#[cfg(any(kani,aeneas_ref))]
+pub mod owned19 {
+    use alloc::vec::Vec;
+    pub fn concat(parts:Vec<Vec<u8>>,index:usize,mut output:Vec<u8>)->Vec<u8> {
+        if index==parts.len() { return output; }
+        let part=parts[index].clone();
+        output.extend_from_slice(&part);
+        concat(parts,index.wrapping_add(1),output)
+    }
+    // One program-table transition, including conflict retention.
+    // The table is represented by unique-key entries; ordering is immaterial
+    // to lookup, while the simulator's public iteration order needs transport.
+    pub fn insert(mut table:Vec<(Vec<u8>,[u8;32])>,index:usize,address:Vec<u8>,answer:[u8;32],collision:bool)
+        ->(Vec<(Vec<u8>,[u8;32])>,bool) {
+        if index==table.len() {
+            table.push((address,answer));
+            return (table,collision);
+        }
+        let (key,previous)=table[index].clone();
+        if key==address {
+            table[index]=(key,answer);
+            (table,collision || previous!=answer)
+        } else {
+            insert(table,index.wrapping_add(1),address,answer,collision)
+        }
+    }
+
+    // Owned recursion for the actual walk's 25 semantic transcript rows.
+    // The callee is unchanged. Both its advanced transcript and semantic
+    // error are retained; no callback success or hash law is asserted here.
+    pub fn semantic_rows<H:aspis_core::Digest32>(
+        mut state:crate::r1_wire::SemanticTranscript<H>, records:Vec<Vec<u8>>,
+        row:usize,mut sem:[aspis_core::field::QM31;25])
+        ->Result<(crate::r1_wire::SemanticTranscript<H>,[aspis_core::field::QM31;25]),super::Error> {
+        if row==25 {return Ok((state,sem));}
+        let record=records[row].clone();
+        let value=state.semantic(row as u8,&record).map_err(|_|super::Error::Semantic)?;
+        sem[row]=value;
+        semantic_rows(state,records,row.wrapping_add(1),sem)
+    }
+}
```

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100
```

## Verbatim premise/event and endpoint diff

```lean
-- R1Z/ProverCommitSeedEvent19.lean
def seedPoint (a : List UInt8) (seed : OracleAnswer) : Prop :=
  a.take ((domain.val.map ProverCommitSaltBytes.byte).length + 32) =
    domain.val.map ProverCommitSaltBytes.byte ++ List.ofFn seed


-- R1Z/ProverCommitSeedEvent19.lean
def augmented {M : Type} (old : Fin 8 → M → Prop) (queries : M → List Entry)
    (i : Fin 8) (r : M × OracleAnswer) : Prop :=
  old i r.1 ∨ (i = 0 ∧ seedGuess (queries r.1) r.2)


-- R1Z/ProverCommitSeedEvent19.lean
theorem seed_mass {M : Type} [Fintype M] [Nonempty M]
    (queries : M → List Entry) (q : Nat) (bound : ∀ m, (queries m).length ≤ q) :
    eventMass (fun r : M × OracleAnswer => seedGuess (queries r.1) r.2) ≤ budget q

-- R1Z/ProverCommitSeedJoin19.lean
structure RunJoin {R M V : Type} [Fintype R] [Fintype M]
    (runtime : R → V) (model : M → V)
    (bad : Fin 8 → M → Prop) (queries : M → List Entry) where
  cp : Coupling R (M × OracleAnswer)
  agreement : ∀ s, ¬ (∃ i, augmented bad queries i (cp.toM s)) →
    runtime (cp.toR s) = model (cp.toM s).1


-- R1Z/PrivacyR1HeadlineDeployed.lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitSeedJoin19.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitSeedJoin19.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))


-- R1Z/ProverCommitSimulatorConcat19.lean
theorem extracted_finite (parts : Parts) (index : Usize) (remaining : Nat) (output : Bytes)
    (count : index.val+remaining = parts.length) :
    sim.owned19.concat parts index output = finite parts index remaining output

-- R1Z/ProverCommitSimulatorInsert19.lean
theorem extracted_finite (table : Table) (index : Usize) (address : Bytes)
    (answer : Answer) (collision : Bool) (remaining : Nat)
    (count : index.val+remaining = table.length) :
    sim.owned19.insert table index address answer collision =
      finite table index address answer collision remaining

```

```diff
diff --git a/docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean b/docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean
index d38a88b65..79a3261ca 100644
--- a/docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean
+++ b/docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean
@@ -0,0 +1,2 @@
+import R1Z.ProverCommitSeedJoin19
+import R1Z.ProverCommitObserverQueries19
@@ -90 +92 @@ existing realBad/selectedBad, not predicates chosen by the implementation. -/
-def RustProverRefinement : Prop :=
+def LegacyRustProverRefinement : Prop :=
@@ -105,0 +108,51 @@ def RustProverRefinement : Prop :=
+/-- Exact adversary-only query suffix of the underlying ordered source. -/
+def realSeedQueries (adv : rust.Adversary) (w : (h).Instance) : (source).RealRand →
+    List ProverCommitSeedEvent19.Entry :=
+  ProverCommitObserverQueries19.real W Pr 8
+    (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs
+    (ProverCommitReencode16.observer ProverCommitReencode16.encode
+      (RomObserverBin.observerMap rust observer_program adv)) x w
+
+def idealSeedQueries (adv : rust.Adversary) : (source).IdealRand →
+    List ProverCommitSeedEvent19.Entry :=
+  ProverCommitObserverQueries19.ideal W 8 eight_pos
+    (P_R1 (h).transport B hB) (simE (h).transport B outputs x)
+    (ProverCommitReencode16.observer ProverCommitReencode16.encode
+      (RomObserverBin.observerMap rust observer_program adv)) x
+
+/-- The explicit deployed obligation. Both sides include the complete public
+view, ordered observer history and observer decision. The exceptions are the
+fixed parser events augmented with a single global seed-guess event on an
+independently retained model seed. Query functions are fixed by the model. -/
+def RustProverRefinement : Prop :=
+  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
+    Nonempty (ProverCommitSeedJoin19.RunJoin
+      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
+      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
+                let v := (source).real h B outputs a x w r
+                (v, (source).observe a v))
+      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
+      (realSeedQueries template outputs x rust observer_program adv w))) ∧
+  (∀ adv : rust.Adversary, Nonempty (ProverCommitSeedJoin19.RunJoin
+      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
+                (v, rust.observe adv v))
+      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
+                let v := (source).ideal (simE (h).transport B outputs x) a x r
+                (v, (source).observe a v))
+      QueryScanIdealHistory.selectedBad
+      (idealSeedQueries template outputs x rust observer_program adv)))
+
+/-- Every previous certificate still suffices. The independent seed is added
+by product extension, so this is an actual implication between premises. -/
+theorem legacy_refinement_implies
+    (old : LegacyRustProverRefinement template outputs x rust observer_program) :
+    RustProverRefinement template outputs x rust observer_program := by
+  constructor
+  · intro adv w hw
+    let join := Classical.choice (old.1 adv w hw)
+    exact ⟨ProverCommitSeedJoin19.of_old _ _ _ _ join.cp join.agreement⟩
+  · intro adv
+    let join := Classical.choice (old.2 adv)
+    exact ⟨ProverCommitSeedJoin19.of_old _ _ _ _ join.cp join.agreement⟩
+
+
@@ -111,4 +164,4 @@ theorem privacy_headline_deployed
-      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
-    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
-      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
-    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
+      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64)) ∧
+    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ≤
+      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ∧
+    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) < 1 / 2^100 := by
@@ -124,9 +177,22 @@ theorem privacy_headline_deployed
-    have hr := QueryScanRealLazyJoin.join_le _ _ _
-      (Classical.choice (refinement.1 adv w hw)).tests
-      (QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr))
-      (ProverCommitModelCore16.real_bad_mass base h B outputs x seed hc₁ hc₂ w)
-      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
-    have hi := scan_coupling_le _ _
-      ((Classical.choice (refinement.2 adv)).tests.toScanCoupling
-        (fun i => QueryScanIdealHistory.selected_bad_mass i))
-      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
+    have hr₀ := ProverCommitSeedJoin19.test_bound
+      (Classical.choice (refinement.1 adv w hw)) (fun run => bit run.2)
+      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
+      (fun r => ProverCommitObserverQueries19.real_bound W Pr 8
+        (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs _ x w r)
+    have hi₀ := ProverCommitSeedJoin19.test_bound
+      (Classical.choice (refinement.2 adv)) (fun run => bit run.2)
+      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
+      (fun r => ProverCommitObserverQueries19.ideal_bound W 8 eight_pos
+        (P_R1 (h).transport B hB) (simE (h).transport B outputs x) _ x r)
+    have hscan : 8 * scanProbability ≤ 8 / (2 : ℚ)^486 := by
+      simpa only [mul_one_div] using
+        mul_le_mul_of_nonneg_left scan_probability_le (by norm_num : (0 : ℚ) ≤ 8)
+    have hr := hr₀.trans (add_le_add
+      ((ProverCommitModelCore16.real_bad_mass base h B outputs x seed hc₁ hc₂ w).trans
+        (add_le_add (le_refl _) hscan)) (le_refl (ProverCommitSeedEvent19.budget (2^64))))
+    have idealMass : eventMass (fun r : (source).IdealRand => ∃ i : Fin 8, QueryScanIdealHistory.selectedBad i r) ≤
+        8 * scanProbability := by
+      exact R0Z.FsAbortBounds.mass_exists_le_card _ _
+        (fun i => QueryScanIdealHistory.selected_bad_mass i)
+    have hi := hi₀.trans (add_le_add (idealMass.trans hscan)
+      (le_refl (ProverCommitSeedEvent19.budget (2^64))))
@@ -158,3 +224,4 @@ theorem privacy_headline_deployed
-    calc _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486) +
-        modelError W Pr L₁ L₂) + 8 / (2 : ℚ)^486 :=
-          t₂.trans (add_le_add (t₁.trans (add_le_add hr hmid)) hi)
+    calc _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
+          ProverCommitSeedEvent19.budget (2^64)) + modelError W Pr L₁ L₂) +
+          (8 / (2 : ℚ)^486 + ProverCommitSeedEvent19.budget (2^64)) :=
+            t₂.trans (add_le_add (t₁.trans (add_le_add hr hmid)) hi)
@@ -162,4 +229,8 @@ theorem privacy_headline_deployed
-           QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) :=
-          QueryScanFreshNumerics.amount_identity _ _ _
-         _ ≤ _ := add_le_add (le_refl _) hk
-  · exact model.2
+           QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) +
+           2 * ProverCommitSeedEvent19.budget (2^64) := by ring
+         _ ≤ _ := add_le_add (add_le_add (le_refl _) hk) (le_refl _)
+  · constructor
+    · exact add_le_add model.2.1 (le_refl _)
+    · apply (add_le_add model.2.1 (le_refl _)).trans_lt
+      exact ProverCommitSeedJoin19.total_lt_target
+        (Nat.le_trans (Nat.add_le_add_right hM 1) (by norm_num)) (Nat.le_refl _)
@@ -167,0 +239 @@ theorem privacy_headline_deployed
+#print axioms legacy_refinement_implies
```

## Final evidence, resource review and remaining deliverable

The overwrite-only source Kani gate `sim::siminsert19small::overwrite` times
out at 600.076 s (exit 124, swaps 0), with cgroup memory peak 6,570,635,264
bytes. The interrupted `/usr/bin/time` child accounting reports 15,480 KiB;
that is retained verbatim but is not presented as the verifier's actual peak
RSS. This failed gate is excluded. No larger cap or unchanged retry follows.
Its source, full stdout/stderr, exact inputs and scope limits are committed.

The preceding broader insertion gate was deliberately stopped at source/proof
shape review. The last process observation recorded 239 seconds elapsed and
5,906,808 KiB child RSS. Stopping its whole scope also terminated the accounting
wrapper, so final wall time, peak RSS and swap measurements are unavailable.
The receipt explicitly records those fields as unknown, launcher exit 241,
and excludes the target; no passing result or invented metrics are claimed.
The replacement changed both source scope and unwind bound, rather than
raising memory. These Kani limitations do not affect the accepted extracted
reference recursion, but leave its general shipped table transport open.

Final Lean target: `R1Z/ProverCommit19Audit.lean`, env J attempt 8704, exit 0,
wall 1.95 s, peak RSS 4,093,916 KiB, swaps 0, source revision `3b9e65518` plus
the exact audit and dependency hashes. All 42 `#print axioms` lines use only
a subset of `[propext, Classical.choice, Quot.sound]`; no new axiom is introduced.
This is one final cached audit of the changed proof dependency cone. The
full frozen release manifest is not replayed while the required full simulator
source target is still not green. No unchanged full regression is run.

`harness/final-audit.py` checks all accepted/excluded Lean receipts and source
snapshots, theorem audit coverage, import-only extraction promotions, valid
LLBC flags, Rust verdicts/caps, current source-prefix identity, unchanged
concurrent-owner modules and absence of committed binaries/LLBC/objects.
Its final result is `final-audit.json`. Historical external templates are
retained only as `.lean.txt` evidence and are never promoted or imported.

What remains is concrete source work, not an additional cryptographic
assumption: close the owned simulator row driver's transcript/parser callee
cone after Aeneas's reproducible context-collapse failure; certify all table
and serialization traversal and their errors; prove the nonzero/counter
schedule and actual view/retry projection; assemble those with the earlier
real-prover certificates into the actual shipped FSExperiments object and
prove both seed-augmented RunJoins. The bounded joint-history law in this
pass can then be consumed by that concrete adapter. Until then the revised
RustProverRefinement is retained and shipped privacy is not established.

Attempts used: J8675–8704, after checking prior host receipts; next assigned
number is J8705, subject to checking host receipts again. All Lean jobs were
serial. Every completed Rust/extraction and Lean job used the requested caps;
all accepted results have zero swap. The only production-file change is the
cfg-gated simulator reference module, and no frozen behavior or security target
is lowered. No concurrent-owner file, wallet or key is changed. No push is made.
