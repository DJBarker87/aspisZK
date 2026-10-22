# Prover commitment part 30

Branch `codex/cx-prover-commit30-20261022`; inherited source
`e78e2c022fddebb3d379963ea09efbca478664a7`. Target not yet established.
Env J 7868–7999 only, skipping existing receipts.

## Stage 1: isolate the native semantic callee

The first modular gate compares `SemanticTranscript::semantic` directly with
`semantic20::semantic`, before any record-vector lookup or semantic-array update.
It checks exact errors, state and row counter on rejection, three ordered hash
calls and their framing/answers on success, and identical pure sampler inputs
and call counts. The owned finite-field substitution is justified by the
retained `ProverCommitFields29.bounded_owned`; its zero-index and length
preconditions are asserted at the call site. The native validator is expanded.
This initial recipe was superseded by the accepted modular gates below.

All harness additions are external, cfg-only host adapters. No tracked file
under `crates/` or `programs/` has changed. Sources, resource receipts and
commands are retained in the part-30 evidence directory.

### Completed validation and callee gates

The native and owned validators are checked independently against the same
byte-level result. Each complete cell requires four little-endian low limbs
below `0x7fffffff` and sixteen zero high bytes. The result is exactly `Ok(())`
or `NonCanonical { row, value: first_failing_cell }`. The native one-cell gate
also covers ignored trailing suffixes. These checks use no field-validation
stubs. The owned gates expand `fields29::finite`; its substitution for
`fields20::validate` uses the unchanged J7866 bounded-owned theorem.

| Target / receipt | Exit | Wall s | GNU peak RSS KiB |
| --- | --- | --- | --- |
| native payload ≤63 / fields30-one-cell-v2 | 0 | 2.743 | 250068 |
| native payload 896 / fields30-exact896-v1 | 0 | 17.397 | 1093756 |
| owned payload 896 / fields30-owned896-v1 | 0 | 24.961 | 1322324 |
| owned payload 32 / fields30-owned32-v1 | 0 | 3.620 | 447928 |
| direct complete row 14 / semantic30-row14-v3 | 0 | 17.353 | 643676 |
| modular all semantic rows / semantic30-all-rows-modular-v1 | 0 | 19.535 | 648632 |

All use zero swap, the requested 6G/8G/0/64 scope and linker flags. Exact
commands, source revision and hashes, dependency fingerprint, scope peak and
raw logs are in `evidence/prover-commit30-20261022/rust-receipts.jsonl` and
`receipts/`. `#print axioms` is N/A for these Rust gates; no new Lean theorem
has yet been claimed.

The modular gate uses an arbitrary *common* validation result. At both call
sites it asserts the same row, payload length and every payload byte against
the original framed record. Byte equality is checked at a fresh arbitrary
in-range index: every index is covered, and the asserted positive payload
length ensures the index assumption never excludes an execution. The separate
native/owned validator gates above justify this congruence cut. The result is
not an assumed successful validation and may reject at any index. The sampler
likewise has an arbitrary common output, with identical input and call count
asserted. All three ordered hash calls are checked separately, including their
framing and answers. Exact semantic errors and the unchanged rejection state
are compared. The accepted scope is every row <25, arbitrary next-row counter,
transcript bytes and framed bytes of length ≤901.

The oversized initial recursive-fuel diagnostic and symbolic variable-length
28-cell diagnostic were stopped for shape review, without a verdict. Their
receipts are excluded. A duplicate-module installer error exited 101; the
installer was corrected and the exact failed source reconstructed against its
hash. None is represented as a proof or memory kill. `source-inventory.json`
checks 661 tracked files against the isolated host workspace: only the two
explicit cfg-only adapter files differ; every other source/configuration pin
matches. No tracked shipped source has changed.

## Stage 2: range-owner and whole-walk composition

J7870 compiles `R1Z.ProverCommitNative30`. `continuation_owned` transports the
source's u8 Range counter through the existing finite-row induction;
`walk_owned` includes initialization; `walk_model` includes both circle points
and the complete Transcript tail; `logged_model` retains the external machine
and ordered read history, including rejection. Exit 0, 1.98 s,
4103840 KiB GNU peak RSS, zero swaps. All four `#print axioms` reports are
`[propext, Classical.choice, Quot.sound]`. J7868/J7869 are excluded elaboration
diagnostics (cast-zero normalization and final reflexivity), retained verbatim.
No failed theorem is accepted and no `sorryAx` appears in the accepted audit.

This Lean owner uses the separately checked semantic iteration substitution;
the source boundary is the recorded Kani proof and structural source binding,
not a new Lean axiom or a declaration pretending to interpret Rust. Its complete
source-to-model attribution at this stage awaited the caller gate, completed below.

The borrowed semantic summary is checked separately against both native and
owned callees in `semantic30-summary-all-rows-v1` (exit 0, 32.496 s,
920484 KiB RSS, zero swaps). This strengthens the earlier callee gate with a
third execution and the same exact state, error and ordered effects.

The initial caller recipes expanded harness input construction or the callee's
parser/oracle body. They were stopped for shape review, and remain excluded.
The replacement caller proof uses a common arbitrary callee result and complete
post-state, checking identical incoming row/state/counter/record bytes and
exactly one call in each context. Both success and every error constructor are
covered. The common post-state is deliberately more general than a genuine
callee outcome; exact callee behavior and effects are supplied by the separate
native/owned callee check. An oracle that panics on any direct caller read
checks that the surrounding caller makes no additional hash query. Thus callee
effects are inserted exactly once at the same program point on both sides,
rather than silently discarded. This is the documented two-harness contextual
congruence argument, not an unverified `stub_verified` annotation.

The native row-14 caller with this complete summary passes
`caller30-row14-context-v1`; stage 3 below completes the remaining rows. No caller expands
field validation. Inputs retain arbitrary transcript bytes/counter, every
semantic array limb, and arbitrary selected record bytes. Fresh arbitrary
index checks cover every incoming record byte and every returned array cell.

## Stage 3: all native iteration cases are green

`caller-matrix.json` checks exactly 25 distinct accepted caller gates, rows
0–24, with identical final caller/callee source hashes and a successful Kani
verdict in every raw log. Rows 14 and 15 now pass with the fully abstract callee
post-state. The record vector has the actual 27-record constructor invariant;
the selected record is arbitrary up to 37 bytes for rows 0–14 and 901 bytes
for rows 15–24. The source's supported shapes have respective maxima 5, 37
and 901 bytes. Oversized framing rejects before hashing; the all-row callee
gate additionally covers arbitrary framed lengths through 901. This does not
claim arbitrary malformed vector lengths satisfy the private constructor
invariant. The other records are unobserved by the literal iteration statement.

The common caller summary abstracts the **entire callee**, not just validation.
Its complete arbitrary post-state, counter, QM31 result and all 12 error
constructors overapproximate genuine outcomes. Each context must call once,
with the same initial transcript/counter, row and record bytes. The source
caller contains no independent hash read (the panic oracle is unreachable).
The separately verified callee proves equal ordered effects, so inserting that
one common effect sequence in either context preserves the external machine
and history. This is the two-harness argument accepted here; the caller alone
is deliberately not represented as proof of its stub.

The existing row induction plus `ProverCommitNative30.logged_model` now composes
this native iteration boundary through all 25 rows, initialization, both circle
points and every Transcript suffix operation. The result is a native walk
source-owner correspondence with the stateful walk model, under the recorded
source/constructor boundary. It is not an FS experiment or a whole-run join.

J7871 is the final changed-cone audit: exit 0, 1.95 s, 4124472 KiB RSS,
zero swaps. All nine complete axiom reports use only the allowed standard
axioms. `closure-check.json` verifies 181 imported object hashes and 159 local
source hashes against the final host closure, with zero differences. The first
closure-check script looked for external Aeneas objects only in the joint
objects directory; it was corrected to use the pinned Env J search path.
No compiler was rerun for that read-only evidence fix.

## Stage 4: demonstrated outer publication/experiment obstruction

The next actual source root was attempted: `sim::sim_e_ablated` at
`sim.rs:396`. `sim30-outer-v1-charon` performs optimized translation with
explicit opaque cuts for the already separated walk and the tape, semantic,
opening and encoding helpers. Charon exits 0 in 35.776 s, 640428 KiB RSS,
zero swaps, **but its LLBC has `has_errors=true`**. The extraction driver
rejects it before Aeneas. This is not an accepted extraction, and no theorem
or source correspondence is inferred from its zero process status.

The five exact transformation errors are mismatched `Iterator` trait clauses
for `BTreeMap::Iter`, `Enumerate`, `BTreeMap::IntoIter`, `ChunksExactMut` and
`Zip`; raw expected/actual clauses and source locations are retained in
`receipts/sim30-outer-v1-charon/stderr.log`. In particular the native publication
loop consumes a BTreeMap iterator with item `(&K,&V)` or `(K,V)`, while the
lowering demands `&T`. Disabling type checks or treating this result as a
compiled source owner would be invalid.

**Exact next interface:** an owned, ordered entry-list transition for the native
`sim_e_ablated` publication loops, certified against `BTreeMap::Iter/IntoIter`
(including conflict retention, key order and all early exits), followed by
an extracted eight-attempt retry/publication owner consuming the certified
walk. The opaque tape/semantic/opening helpers must retain their actual
source contracts; making them callbacks is not a discharge. The real side
also requires the corresponding `prove_masked_retrying_with` publication and
entropy/reservation transition, not just a prepared `Records` argument.

These source functions return proof bytes, programming tables and failure
status; `walk` returns only challenges from already prepared records. The
`FSExperiments` target instead requires both real/ideal `ROMView` values and
the adaptive observer's ordered oracle transcript and decision. No certified
outer owner currently supplies that conversion. The retained entropy model
also explicitly retains OS failures and zero-draw exhaustion; those cannot
be silently replaced by uniformly nonzero secrets. J7871 audits the existing
`os_error`, `zero_draws` and unrestricted-runtime countermodel for this reason.

Stop at this failed source-lowering boundary. `shippedProverExperiment` is not
constructed; neither real nor ideal WholeRunJoin outside realBad/selectedBad,
seed-guess and fuel events is claimed. `RustProverRefinement` remains explicit.
No assumption, quantifier, carrier, failure event or numerical budget was
changed; zero refinement premises were removed. Target not yet established.

No tracked file under `crates/` or `programs/` was edited (enforced by
`final-check.py` against inherited `e78e2c022`); therefore the shipped-file
rebuild rule was not triggered. The unchanged part-29 frozen ELF evidence is
reused, not rerun or attributed to changed production bytes. No unchanged
full manifest or runtime suite was rerun: the outer source preflight is not
green. No task wallet/key was created or deleted. All host work used isolated
job directories, the requested resource caps and linker limits; reservation
waits were honored. No other worktree was changed, and no push/merge occurred.


The 25 accepted caller receipts total 331.441 s wall time (two independent
capped lanes); the largest individual GNU peak RSS is 629360 KiB and the
largest scope peak is 681431040 bytes. Row 14 takes 10.062 s / 515268 KiB;
row 15 takes 13.386 s / 610496 KiB. Every exit is 0 and every swap count is 0.

## Verbatim endpoint before/after

The module is byte-identical to `26b922be6`. Surrounding parameters and local
notations are unchanged. These are unchanged statements, not a completed
specialization or a deletion claim. Full modules, statement excerpts and the
empty diff are retained under the part-30 evidence `endpoint/` directory.

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

## Final source pin

All final Lean modules and exact historical/current Rust adapter snapshots are
committed at `3b1b30838`. `final-source-revision.json` binds every completed
receipt's Rust snapshots to that revision and the native source base
`e78e2c022`; it separately pins both new Lean modules. There are 32 accepted
Rust gates, excluding every stopped/error diagnostic and the invalid outer
LLBC. The handoff commit changes only source-pin/report metadata.
