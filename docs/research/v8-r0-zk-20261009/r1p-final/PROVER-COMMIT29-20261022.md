# Prover commitment part 29

Branch `codex/cx-prover-commit29-20261022`; inherited revision `6a86aa5dc`.
Endpoint comparison base `26b922be6`. Target not yet established.
Env J 7840–7999 only, skipping every existing receipt.

## Stage 1: owned native semantic iteration

The cfg-only `sim::owned29::semantic_step` owns the incoming transcript,
record and semantic array. It calls the retained P6 `semantic20::semantic`,
with its `fields20` owned validator, then maps errors and writes the sampled
array cell. The unchanged shipped iteration remains the comparison target.
The two retained helper modules are now present under cfg(kani)/cfg(aeneas_ref)
in `r1_wire.rs`; production configurations do not include them.

`step29-owned-v3` extracts the entire owned reference with **no opaque cut**:
Charon exit 0, 33.952 s, 577660 KiB RSS; Aeneas exit 0, 1.281 s,
116336 KiB RSS; both zero swaps. The earlier direct-native-callee reference
failed in `InterpReduceCollapse.ml:1991` while translating the borrowed field
validator. `step29-v2` cut that validator and succeeds, but is excluded as a
completed native semantic refinement. V3 replaces that route with the retained
owned semantic reference, rather than asserting the opaque validator correct.

`port-step.py --check` compares all 25 reused extracted definitions with the
retained semantic namespace and retains the new owner body exactly, apart from
the nominal verifier Error namespace. One dependency has the raw generator's
`32#i32` shift operand where the pinned library requires `U32`; the retained
`32#u32` annotation is used. `shift_count` audits the equal nonnegative numeric
operand. The raw generated text is retained; it is not represented as compiling
unchanged against the older shift signature.

J7840 compiles the extracted owner port. J7842 proves `extracted_step`, the
numeric annotation check, and `iteration_effects`, installing the concrete
oracle machine. Exit 0, 1.87 s, 4132272 KiB RSS, zero swaps; all three axiom
reports are `[propext, Classical.choice, Quot.sound]`. J7841 is an excluded
failed diagnostic, not an accepted proof. No source-to-model claim is inferred
from the reference alone.

The no-stub empty-record Kani preflight was stopped after pathological symbolic
sampler expansion. Its receipt is retained. The replacement uses an arbitrary
shared sampler result, checks equality of both sampler inputs and call counts,
and separately replays every ordered Digest32 call and answer. The empty-record
replacement passes (1762 checks; 7.131 s total, 533792 KiB RSS, zero swaps).
This is still just a preflight: the all-record check is pending.

The shipped-file gate rebuilt default, devnet and pool from a separate exact
tracked-source snapshot after the cfg additions. All are byte-identical to
the frozen artifacts: respectively `dfc2a91a…`, `fb2fc048…`, `121f3e29…`;
full hashes, sizes, `cmp` status, command, cap and resource receipts are in
`frozen-elf-final-check.json`. The first build hit the 64-task limit before
four-CPU affinity was applied; the next found an incomplete workspace snapshot.
Both failures and their environment/snapshot fixes are retained. Final builds
exit 0 in 6.066/2.305/0.363 s, peak RSS 203936/204000/100816 KiB, zero swaps.
No cap was raised. Build time was optimized compilation/linking.

Pending: complete per-iteration Kani gate, finite-row induction, native walk
composition, shipped experiment and both WholeRunJoins. No refinement premise
has been removed. Target not yet established.

## Stage 2: finite row induction and composed stateful walk

`ProverCommitRows29.rows_model` is a symbolic induction for every prefix
`row.val+n≤25`. It composes the extracted owned step and proves equality with
`ProverCommitSemanticRows28.rows` after explicitly forgetting the local state
on inner semantic errors. It retains malformed records, array/index failures,
divergence and all externally observable machine effects. The theorem is
polymorphic over lawful monads and lawful Result lifting; no oracle, sampler,
privacy or implementation-join hypothesis is added.

`ProverCommitWalk29.suffix_source` reconstructs the retained complete suffix
by definitional equality. `continuation_model` composes the finite rows, both
circle points and every Transcript tail operation. `walk_model` includes the
actual extracted initialization. `logged_model` instantiates the induction
with the extracted oracle machine and ordered read history, including on error.
`walk_effects` installs the concrete reference machine in this composition.
The result projects only the internal local state/trace fields that native
`walk` does not return; the external machine/history are retained.

J7846 passes the four generic row audits (2.08 s, 4151596 KiB RSS). J7850
passes all five composed-walk audits (2.11 s, 4140088 KiB RSS). Both exit 0,
zero swaps; every audit is a subset of the allowed standard axioms. Earlier
syntax/inference/bind-associativity diagnostics are retained and excluded.
No resource or kernel limits were raised. These are owned-reference-to-model
results; the native connection remains gated on the per-iteration Kani result.

The all-record Kani preflight exposed a proof-shape issue: a global unwind of
904 also expanded the recursive 32-byte validator up to 904 calls, even though
a semantic record has at most 28 field cells. It was stopped before memory
pressure. `show-step-loops` identifies the native validation and byte-comparison
loops. The replacement uses global unwind 40 and `memcmp.0:904`, retaining
unwinding assertions; no source input bound or covered error is weakened.
The replacement gate is pending. No whole-function harness has been used.


## Stage 3: record lookup, native range counter and final source audit

The original P6 step accepted an already selected row record. It did not cover
the native `r.semantic[row]` lookup. The added `owned29::iteration` selects and
clones that record before calling the owned step. `iteration29-v1` extracts
this complete one-iteration owner without opacity (Charon 31.546 s,
578644 KiB RSS; Aeneas 1.150 s, 114048 KiB RSS; exit 0 and zero swaps).
`extracted_selected` reconstructs that owner including index failure and clone;
`selected_effects` installs the concrete oracle machine in it.

`range_model` relates the native u8 Range counter to the bounded usize row
owner, with symbolic no-wrap/increment lemmas. J7858 passes all five step audits
(2.01 s, 4093136 KiB); J7859 passes all eight row audits (2.16 s, 4114124 KiB);
J7860 refreshes the five walk audits against those changed dependency hashes
(2.03 s, 4100096 KiB). All exit 0, zero swaps, allowed axioms only. J7853 was
refused by the reservation preflight before a compiler launch; it is recorded
separately and was not represented as a Lean replay.

J7861 is the final changed-cone axioms audit: exit 0, 1.85 s,
4131592 KiB RSS, zero swaps. All 22 lines (18 new theorems, both extracted
owners and both retained endpoints) use only the allowed standard axioms.
This remains a reference/source-owner audit, not evidence that the missing
native per-iteration gate passed or that a concrete FS experiment exists.

All three frozen ELFs were rebuilt again after adding the record-selection
owner: exits 0, 2.743/2.266/0.377 s, RSS 200040/202720/100784 KiB, zero swaps.
All three remain byte-identical; `frozen-source-inventory.json` compares all
492 tracked shipped files, manifests/lock and Cargo configuration with the
exact rebuilt snapshot, with no differences.

The symbolic-row 901-byte check `step29-records-v4` timed out with exit 124
at 600.483 s and no verdict. The cgroup peak was 6702342144 bytes. GNU time
reported only the timeout parent's 15488 KiB RSS, so that value must **not**
be promoted to the solver peak: direct process sampling reached 6525556 KiB.
The scope used zero swap. No counterexample or memory-kill is inferred.

Replacing the symbolic row with concrete row cases makes the complete native
lookup preflight for row 0 / an empty record pass (13.052 s, 1102052 KiB RSS,
zero swaps). This is an error-path check, not the full 25-row gate. Row 14
with arbitrary records up to 37 bytes and row 15 up to 901 bytes are pending.
Every check compares the literal native iteration statement with the extracted
owned iteration, using arbitrary state/semantic cells and the 27-record
constructor invariant. Ordered hash framing/answers and all errors are checked.
The only callee congruence cut is the same pure sampler's arbitrary common
result, with identical input and call count required on both executions.


## Stage 4: certified finite field-cell substitution and stopping point

The three earlier failed recipes were not retried unchanged with a larger
memory cap. The diagnostic `row14-status6-diagnostic` recovers the precise
CBMC error hidden by Kani's terse status 6: `too many addressed objects`,
maximum `2^10 = 1024`. It exits 6 after 95.871 s, peak RSS 3751724 KiB,
zero swaps. This is not a source counterexample. Row 2's arbitrary root record
(up to 37 bytes, with native lookup and the success/error paths) passes:
`iteration29-row2-root-v1`, exit 0, 15.430 s, 675460 KiB RSS, zero swaps.
The corresponding row-14 field-bearing gate with 12 object bits was stopped
for proof-shape review; it is excluded, not called a passed check.

`r1_wire::fields29::finite` adds explicit field-cell fuel to the **owned
reference**, retaining each source parse, error, clone and wrapping index.
It is extracted in full without a native opaque boundary (`fields29-v1`:
Charon exit 0, 29.889 s, 576944 KiB; Aeneas exit 0, 0.861 s, 102256 KiB;
zero swaps). `port-fields.py --check` checks every reused field definition
and copies the new function body exactly into the retained nominal namespace.

`ProverCommitFields29.finite_source` proves its equality with the retained
Nat-bounded validator for arbitrary fuel/payload/value. `bounded_owned` then
uses the existing `ProverCommitFields20.extracted_finite` to prove exact equality
with `fields20::validate` whenever `payload.length < 32*(fuel+1)`. It preserves
the exact first failing index, short suffixes, errors and divergence. J7866
passes these three audits and the extracted helper audit: exit 0, 1.30 s,
2542108 KiB RSS, zero swaps, standard axioms only.

The replacement Kani adapter checks that length bound by **assertion**, along
with the incoming zero field index; it does not assume either condition. It
uses one field cell for row 14 and 28 for semantic rows 15–24. The native
validator is unchanged. Its row-14 loop is bounded to two unwind checks with
unwinding assertions enabled. This exact input-size theorem justifies replacing
the owned validator call; no native validation/source agreement is assumed.
This field-cell fuel leaves the protocol's sampler fuel events and charges
unchanged.

**Demonstrated obstruction:** even that complete native row-14 iteration gate,
`iteration29-row14-fueled-v1`, times out with exit 124 after 600.136 s.
Cgroup peak memory is 6614237184 bytes; observed individual solver RSS reached
6439948 KiB, with zero swap. The GNU-time receipt's 15816 KiB is only the killed
timeout parent's RSS and is not a valid solver peak. The fixed row-15 gate
also timed out: exit 124, 600.291 s, cgroup peak 6691713024 bytes; the attached
monitor recorded 6551728 KiB aggregate scope RSS (a sampled lower bound on
full-lifetime peak), zero swap. No counterexample, successful per-iteration
certificate or full native walk identity is inferred from either timeout.

**Exact next interface:** a checked native/owned semantic-callee contract,
consumable by the iteration caller without re-expanding its borrowed field
validation. At minimum it must connect native `validate_record_fields`
(`r1_wire.rs:51–59`) to `fields20::validate` / the now-certified finite helper
on the row-14 32-byte and row-15–24 896-byte payloads. Success versus rejection
is sufficient after the caller's `map_err(Error::Semantic)`, but the contract
must preserve unchanged transcript state/no hash before validation, then the
same three ordered hash reads, return value and advanced state on success.
The retained per-cell checks are not silently promoted to that callee/caller
contract. The next deliverable is that modular contract plus a completed
row-14 gate, then the row-15 gate and all-row bridge; no whole-function harness.

The 25-row induction and both-circle/Transcript composition are **reference to
model** equalities until this source contract is certified. Thus stage (2)'s
native per-iteration gate is incomplete, and stage (3)'s full native owner
identification is not claimed. `shippedProverExperiment`, the real and ideal
WholeRunJoins, retry/programming/serialization and endpoint specialization
remain open. No assumptions, quantifiers, failure events or numerical budgets
were changed; zero refinement premises were removed. Target not yet established.

J7867 is the final updated axiom audit after the new source/helper proof:
exit 0, 2.31 s, 4129844 KiB RSS, zero swaps; 26 complete axiom lines (21 new
theorems, three extracted owners/helpers, two retained endpoints), all subsets
of `[propext, Classical.choice, Quot.sound]`. The previous audit was refreshed
because its source/import closure changed. `closure-check.json` checks the
179 final imported object hashes and all seven current source hashes, with
zero differences. No unchanged full manifest was rerun: its source preflight
is not green. Historical diagnostics and source snapshots are retained.

All three ELFs were rebuilt once more after the cfg-only finite helper was
added. All exit 0 and remain byte-identical: 5.766/2.193/0.361 s,
203056/202920/100812 KiB RSS, zero swaps. Final exact hashes and byte comparisons
are in `frozen-elf-final-check.json`; all 492 shipped source/configuration pins
match the rebuilt snapshot. The proof workspace differs only by the two
explicit cfg-only Kani adapters; accepted preflights have exact source snapshots.

All host builds used the requested 6G/8G/0/64 scopes, optimized extraction/SBF
compilation and four-job/linker limits. Kani uses its native GOTO backend rather
than executing a debug Rust arithmetic gate. Reservation refusals/waits are
retained; no other worker or worktree was modified. Build-generated task keys
are retained at the recorded host paths with 0600 permissions; no key material
is committed. No push or merge was performed. Stop at the demonstrated source
callee-contract obstruction above.

## Verbatim endpoint before/after

The endpoint file is byte-identical to base `26b922be6`. These statements use
unchanged surrounding parameters and local notations. The full module copies,
SHA-256 identity record and empty deletion diff are committed with the evidence.
This is zero-premise deletion, not a completed specialization.

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
