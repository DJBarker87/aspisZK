# Prover commitment part 21

Base `ec5946193`; branch `codex/cx-prover-commit21-20261021`.

Target not yet established. This packet records focused partial results; every claim below is
limited to the named source/model boundary. No shipped source edits, no
concurrent-owner edits, no pushes.

## Stage 1 — single insertion and table composition

The verified four-byte key-comparison contract (`table-key-v1`) passes
(exit 0, 1.569 s, 295956 KiB). The single owned entry with an arbitrary
first-hit prefix/suffix summary (`table-entry-v1`) passes using that verified
stub (exit 0, 2.914 s, 427616 KiB). Both use unwinding assertions, swaps 0,
6G/8G/no-swap/64-task caps. The Rust gate is an owned source-shaped branch;
it does **not** execute arbitrary std::BTreeMap insertion or arbitrary-length
key comparison. Its summaries are justified only for the abstract entry
representation, not the shipped library representation.

`ProverCommitTablePrefix21` proves `lookup_append`, `insert_append_miss`,
`overwrite_after_prefix`, and `entry_collision` by induction on an arbitrary
finite prefix. The overwrite theorem preserves the prefix and suffix
verbatim and gives the exact sticky flag. It composes with part-20 writes
and adaptive history theorems, without a key-uniqueness or size assumption.
J8733/J8734 are excluded syntax/elaboration failures; changed-source J8735
passes (exit 0, 1.34 s, 2516444 KiB, swaps 0; standard axioms only). Exact
snapshots and dependency fingerprints are in `lean/attempts-8733-8736.jsonl`.

`ProverCommitKeyCompare21.vec_eq` proves arbitrary-length Aeneas byte-Vec
comparison equals List equality (J8739, exit 0, 1.23 s, 2522828 KiB;
J8738 excluded). `ProverCommitTableKeys21.extracted_keys` installs it
through the **actual extracted owned insertion loop** for arbitrary finite
table lengths, preserving indexing/update/growth errors and array value
comparison (J8742, exit 0, 1.28 s, 2530436 KiB). All standard axioms,
zero swap. This is a universal owned-source helper theorem, not the
std::BTreeMap representation proof.

A changed actual `ProgramOne` overwrite-flag gate eliminates key allocation
and comparison by using the empty key, retaining arbitrary 32-byte old/new
answers and an arbitrary initial flag. It still reaches the MemoryHigh
region and is stopped for shape review (exit 1, 90.620 s, 6378692 KiB,
swaps 0). This is excluded, not a counterexample or a passed source gate.
No unchanged larger-cap retry occurs.

No universal std::BTreeMap-to-entry theorem is claimed. A symbolic prefix
summary alone cannot discharge the source-library representation invariant.

## Stage 2 — later simulator traversal

The first suffix extraction isolates the next failure to native TLS tracing:
Charon v1 emits an opaque CircleRow discriminant and is excluded; adding
the enum declaration produces error-free LLBC, but Aeneas v2 fails in
`std::thread::local::LocalKey::with` (exit 2, 2.144 s, 374528 KiB).
An owned byte-trace version translates but exposes external iterator, field
serialization and query-sampler templates. Those templates are retained
as inert `.lean.txt`, never imported or accepted as axioms.

The accepted **generic control** reference moves native trace entries to a
returned Vec of field values and gives gamma, ordinary, qm31 and q22
selection as explicit policy parameters. It preserves all eager squeeze /
advance calls, row labels, payloads and query rejection; it adds no hash
or sampler equation. The concrete policy functions are not proved by this
reference. Circle rows 25/26 remain outside this accepted suffix.

`sim-tail-control-v2` translates with no external templates (Charon exit 0,
32.303 s, 577028 KiB; Aeneas exit 0, 3.281 s, 489104 KiB). Types J8740
and Funs J8741 compile (1.38 s / 2539196 KiB and 5.88 s / 2782816 KiB).
Port changes are only narrowed imports and declaration-order discriminant
expansions, with exact raw/promoted hashes and diffs in `extraction/control21`.
Generated resource settings are unchanged.

`ProverCommitTail21.tail_schedule` decomposes the extracted reference into
rows 27–30 followed by query/rho continuation. `query_failure` retains the
post-query state and previous trace and omits rho. `query_success` retains
the final row-32 state and trace. `semantic_continuation` transports the
accepted 25-row finite source equation through every continuation consuming
its entire result, including errors/state. It does not instantiate the
missing circle/source-carrier/policy/TLS join. J8746 passes (exit 0, 1.32 s,
2531256 KiB, swaps 0; all standard axioms). J8743 passed an earlier focused
version; J8744/J8745 are excluded schedule elaboration failures.

Two optimized differential fixtures instantiate the policy with the actual
source samplers and compare the original `walk` against the part-20 owned
25-row cone, actual circle methods, and the new generic suffix. Both the
success and all-zero/query-rejection paths agree on returned result, the
**entire ordered request/answer history**, and the serialized native trace.
The rejection path retains four scalar trace entries; success has 27.
`tail-runtime-v1` passes (exit 0, 5.171 s, 357184 KiB, swaps 0), under
6G/8G/no-swap/64 tasks. These are fixtures, not universal source refinement.

## Stage 3 — nonzero loop and endpoint

`ProverCommitNonzeroStream21` strengthens the part-20 obstruction: a single
consistent callback can answer zero on every target-stream address while
retaining every answer on every other stream, for all seeds, attempts,
counters and counter wraparound. `frame_stream`, `target_answer`,
`other_answer`, `target_zero_prefix` pass J8737 (exit 0, 2.10 s,
4042696 KiB, swaps 0; standard axioms). J8736 is an excluded simp failure.

Thus finite *protocol dimensions* alone do not imply a uniform bound for
the generic coin callback. The transcript and root streams can be held
fixed while tape-stream nonzero search consumes any finite fuel without
success. This result does not instantiate an accepted P_R1 challenge draw,
does not identify concrete HOST_HASH with the generic callback, and does
not assign a probability to this behavior. Those qualifications matter: it
is not a proof that an actual admitted source run diverges, nor an attack.

No artificial abort, cap, new bad event or total experiment is introduced.
To construct the requested shipped experiment still requires either a
concrete hash termination argument, or a source-faithful treatment of
divergence and its probability/coupling, followed by both WholeRunJoins.

## Endpoint and premise audit — verbatim before/after

No new deployed endpoint is justified by these results. The before and after
statements are **identical**, with no premises discharged, added, hidden, or
renamed at the deployed endpoint. In particular the explicit policies of
`control21` are not installed as a proved source instance. The two RunJoins
remain inside RustProverRefinement, with the same adversaries, carriers,
public views, seed-query exceptions, bad events, and privacy conclusion.

Before (`ec5946193`):

```lean
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

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) < 1 / 2^100
```

After (this branch):

```lean
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

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) < 1 / 2^100
```

`endpoint.diff` is empty. The final audit also prints the deployed theorem's
axioms, rather than treating its import as proof of its hypotheses.

## Final verification and handoff

J8747 (`R1Z/ProverCommit21Audit.lean`) passes: exit 0, wall 1.73 s,
peak RSS 4100792 KiB, swaps 0; revision `a00e0e65a` plus exact snapshot
SHA/dependency fingerprint. Its 24 full axioms lines cover every new theorem,
the extracted control functions, and the retained endpoint; all use subsets
of `[propext, Classical.choice, Quot.sound]`. `final-audit.json` checks
source snapshots, accepted receipts, promoted hashes, scope caps and the
unchanged endpoint. Attempts J8733–8747 are consumed; next J8748, subject
to the shared receipt check. No full frozen release replay is claimed: the
universal source closure is not green. No unchanged regression is rerun.

Host source inspection found an inherited proof-only coin18 block inserted
before the already-shipped owned19 module in `sim.rs`; the original source
is byte-identical after removing exactly that documented block for comparison.
The other bodies match directly. `source-prefix-binding.json` records raw
instrumented hashes and the projection; `sim.rs.source-body.diff` retains
the exact inherited addition. No accepted new extraction invokes coin18.
All new instrumentation is host-only and explicitly guarded. No local file
under `crates/` or `programs/` changes, so D129's three-ELF result is reused
for the unchanged source base; no fresh artifact equivalence is claimed.
No concurrent-owner module, wallet or key is changed. No pushes. No SSH
session exceeded twenty minutes without output.

**Target not yet established.** The demonstrated source obstructions are
the allocator/tree overwrite formula growth and the TLS/iterator/query
external boundaries in direct suffix extraction. The formal obstruction is
the absence of a universal finite nonzero bound for generic consistent
callbacks, even with the other coin streams preserved. These results do
not disprove an off-bad probabilistic coupling. They prevent honestly
constructing the requested *total shipped* experiment from the present
finite-schedule adapter or removing RustProverRefinement.

Next concrete deliverables:

1. A universal std::BTreeMap insertion/lookup/enumeration representation
   proof, with per-entry library contracts; additional bounded prefix
   summaries alone cannot establish it.
2. Concrete circle rows 25/26, sampler-policy and TLS trace identification,
   plus the logical/compact caller carrier and source iterator joins.
3. An admitted-input termination proof for the concrete source hash, or a
   source-faithful divergence law/coupling within the fixed security contract.
   The source's attempt cap does not bound the inner nonzero loop.
4. Remaining programming/serialization/error/retry assembly, then the
   actual shippedProverExperiment and ideal-side and real-side WholeRunJoins.
