# Prover commitment continuation 32

Base: 26b922be6. Branch: codex/cx-prover-commit32-20261022.
Blocked at the native ordered-map transition gate. Target not yet established.

D143/D144 govern this continuation: sorted owned association lists and small
recursive extracted functions; public statement bytes, submitted proof bytes,
and answers to adversary queries are the observable. Timing and other side
channels are outside the privacy contract. Internal programming tables and
attempt counts are not published protocol outputs.

Stage 1 starts with sorted numeric-map insertion, lookup and query-order
publication. These are proof-only references; no native-owner equality is
claimed merely by adding them. The remaining stages are the complete
publication driver, eight-attempt owner, real entropy/reservation owner,
source-to-FSExperiments conversion, both WholeRunJoins and deletion-only
endpoint specialisation. RustProverRefinement remains explicit.

Recovery stage: the in-flight Kani process survived the capacity interruption;
its existing capped run is being collected before a replacement is considered.
The three small roots (`index_insert`, `publish_queries`, `merge_program`)
translate with `has_errors=false` and Aeneas exits 0. The generated import
`Aeneas` is mapped to the pinned env J imports `Aeneas.Std` and
`Aeneas.Tactic.RustAttributes`, as for the prior continuations.

Env J 9021–9024 compile the insertion and query-publication generated modules.
Attempt 9029 proves `R1Z.ProverCommitPublication32.next_cursor` and
`lookup_total`: every finite table lookup from an in-bounds cursor terminates
without an indexing error. This is totality, not yet the sorted-map refinement.
Both print `[propext, Classical.choice, Quot.sound]`; exit 0, 1.37 seconds,
2,533,728 KiB peak RSS, zero swaps. Rejected attempts 9025–9028 are retained.
Exact source snapshots, hashes, dependency fingerprints and compiler logs are
in `evidence/prover-commit32-20261022/lean/`; extraction/Kani logs and source
pins are beside them. No endpoint premise has been removed.

The focused recursive proofs now also establish:

- `lookup_refines`: exact early-stop sorted-list lookup for all finite tables;
- `publish_refines`: exact query-list order, including repeats, absent entries,
  and the unchanged byte-append failure behavior;
- `tail_refines`: tail copying equals prefix concatenated with the unprocessed
  suffix, under the explicit capacity bound;
- `insert_refines`: exact ordered-list insertion, replacement and returned old
  value for all finite tables under the explicit capacity bound.

The pure-list specifications are definitions in the proof modules, not assumed
successful source calls. Sortedness/map correspondence is a separate obligation:
these theorems alone do not certify the native BTreeMap owner. Accepted focused
checks are J9032 (publication), J9034 (tail), J9035 (generated programming module)
and J9038 (insertion). Axioms are subsets of `[propext, Classical.choice,
Quot.sound]`; all accepted checks exit 0 and report zero swaps. J9030,
J9036–9037 are rejected proof drafts, retained with exact errors.

The recovered insertion v5 completed with exit 124 at 600.105 s and a
6,594,351,104-byte scope peak, zero swaps. Lookup v1 likewise timed out at
600.161 s with a 6,631,309,312-byte scope peak. These are not accepted Kani
results. The revised gate constructs a sorted pre-state directly; the selected
observation variant compares a universally selected entry and byte instead of
whole-map/vector equality. Unwinding assertions remain enabled. No cap was
raised and no unchanged full regression was repeated.

## Verbatim endpoint before/after

The endpoint is byte-identical to `26b922be6`. This records zero premise
deletions, not a completed specialization. Full before/after modules and an
empty diff are retained under `endpoint/`; all surrounding parameters,
quantifiers, carriers, failure events, and budgets remain unchanged.

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

## Frozen artifacts

The shipped-file rule is satisfied for the Rust changes in this branch.
All three commands use optimized SBF compilation/linking, four build jobs,
four linker threads and the requested 6G/8G/zero-swap/64-task scopes.

| ELF | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| default | 0 | 2.735 | 204044 | 0 |
| devnet | 0 | 3.164 | 203440 | 0 |
| pool | 0 | 0.403 | 100724 | 0 |

Each `cmp` exits 0. SHA-256 values are respectively
`dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`,
`fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78`,
and `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
`pins/frozen-elf-final-check.json` contains exact commands, sizes, source hashes
and receipts. `frozen-source-inventory.json` checks all 494 tracked shipped
inputs against the rebuilt snapshot, with zero differences. The build source
revision is `9fa279bcdb2c4680ba5562f8396cfb738c65fe69`; subsequent changes are
proofs, harnesses and evidence. No binary or compiled Lean object is committed.

## Latest focused proof receipts

All entries below exit 0 with zero swaps. Every new theorem's complete axioms
line is retained in `lean/attempts.json`; accepted axioms are only subsets of
`[propext, Classical.choice, Quot.sound]`. `final-proof-audit.json` checks the
final source hashes against these accepted attempts, so rejected drafts are
not attributed to the accepted proof bytes.

| Final module | Env J attempt | Wall s | Peak RSS KiB |
|---|---:|---:|---:|
| AspisR1IndexInsert32.Types | 9021 | 0:01.49 | 2509796 |
| AspisR1IndexInsert32.Funs | 9022 | 0:01.37 | 2521460 |
| AspisR1Publish32.Types | 9023 | 1.41 | 2506064 |
| AspisR1Publish32.Funs | 9024 | 1.40 | 2517148 |
| AspisR1Program32.Types | 9033 | 1.20 | 2513696 |
| AspisR1Program32.Funs | 9035 | 1.50 | 2530028 |
| R1Z.ProverCommitPublication32 | 9032 | 1.93 | 2551384 |
| R1Z.ProverCommitSorted32 | 9040 | 6.24 | 2516828 |
| R1Z.ProverCommitProgram32 | 9039 | 1.70 | 2540580 |
| R1Z.ProverCommitMapInvariant32 | 9043 | 1.39 | 2524124 |

`byte_order_refines` proves proper-prefix and lexicographic order for arbitrary
finite byte strings. `insert_old` and `lookup_insert` relate replacement to
prior/future duplicate queries. `insert_sorted` proves strict key order and
uniqueness are preserved from the empty list; `insert_mem` bounds the new
entries to the new key/value or an old entry. None assumes the desired native
map equivalence. The complete programming-table owner is not proved by the
byte-comparator theorem or by compiling its generated module.

The isolated native gate includes the exact `sim_owned32.rs` source file,
without copied implementation or stubs, in a dependency-free crate. It uses
the same Kani Rust BTreeMap and narrows the unwind bound from 12 to 4 for the
at-most-two-entry pre-state (at most three post-insert entries). Unwinding
assertions remain enabled: an insufficient bound is a failure, not an
assumption. This is a source/recursion-shape diagnostic, not a relaxation of
the theorem's quantifiers. It ultimately exits 124 at 600.253 seconds; the final receipt is retained.

Final accepted Lean source bytes are pinned by commit `3384569ae` and checked
against the focused attempt hashes by `final-proof-audit.json`. Historical
attempt metadata identifies the initial Rust base `113bbc4f2` plus the exact
per-attempt Lean source overlay and imported-object dependency fingerprint;
it must not be read as claiming those later proof files existed in that base.
Rejected drafts remain distinct source snapshots. The generated module import
mapping is the only compatibility edit to the Aeneas output.


## Demonstrated obstruction and exact next interface

The native gate remains unaccepted after changing setup to direct sorted
pre-states, changing whole-output comparison to a universally selected entry
and byte, changing solver/object representation, restricting to empty or
singleton pre-states, and finally isolating the exact source in a minimal
crate with unwind 4. The interruption was recovered, and the requested
`sim::publication32::insert_replace_order` was rerun with changed harnesses.
These are bounded resource/tool failures, not counterexamples or an
impossibility result about the source algorithm.

Final completed diagnostic timeouts (all exit 124 and zero swaps):

| Gate | Wall seconds | Scope peak bytes |
|---|---:|---:|
| publication32-insert-v5 | 600.105 | 6594351104 |
| publication32-insert-v6 | 600.199 | 6601904128 |
| publication32-insert-v7 | 600.313 | 6659194880 |
| publication32-lookup-v1 | 600.161 | 6631309312 |
| publication32-lookup-v2 | 600.287 | 6665220096 |
| publication32-entry-v1 | 600.003 | 6268243968 |
| publication32-single-insert-v1 | 600.395 | 6681976832 |
| publication32-isolated-insert-v2 | 600.253 | 6612606976 |

The last command's reported GNU-time peak RSS is 15,304 KiB. Timeout can
terminate descendants before GNU time accounts for their RSS, so this wrapper
metric is not represented as the actual prover-process peak. The aggregate
scope peak is 6,612,606,976 bytes; sampled live CBMC RSS exceeded 6 GiB. Full
commands, caps, times, source/input pins and N/A axioms fields are joined in
`rust-receipts.jsonl`. No cap was raised and no killed-by-pressure job was
retried unchanged. Each ten-minute run stops at its mandatory review point.
The isolated v1 CLI diagnostic exits 2 because the unstable CBMC options flag
was missing; v2 adds that flag. Neither is reported as a successful Kani gate.

**Exact next interface:** establish the native `BTreeMap<usize, Vec<u8>>`
insertion/replacement/ordered-iteration transition against
`R1Z.ProverCommitSorted32.insert`: starting from the ordered entries of the
native pre-state, `index_insert(..., 0, [])` must return the native post-state's
ordered entries and exactly the previous value returned by `BTreeMap::insert`.
The pending bounded target is
`sim::publication32::insert_replace_order`, with exact minimal harness/source
pins under `harness/map-gate/` and `publication32-isolated-insert-v2-inputs.json`.
A passing diagnostic is still a bounded check; the general native/TrustedStd
interface must remain explicit until its required source correspondence is
established. Lazy entry behavior, folded publication, and the programming map
must receive their own transition checks before owner composition.

After that boundary, the next source driver must own base/ext coefficient
vectors and the query counter, retain the actual `encode_at` contracts,
replace duplicate opening entries, and serialize in the original query order.
The numeric-map and byte-publisher proofs here do not calculate those
opening cells or construct the complete `sim_e_ablated` publication owner.
The recursion-style extraction failure from D144 is bypassed for the small
roots; the source-to-native-map verification boundary is not discharged.

## Retained obligations and stopping state

Stage 1 is partial. The complete opening/folded/programming owner and its
composition remain open. Stages 2–5 were not completed: there is no certified
eight-attempt publication owner, real entropy/reservation publication owner,
source-to-FSExperiments conversion, concrete `shippedProverExperiment`, or
concrete real/ideal WholeRunJoins. `RustProverRefinement` is retained exactly;
zero premises, quantifiers, carriers, failure events or budgets changed.
No new cryptographic assumption is introduced.

The inherited entropy source boundary continues to distinguish immediate OS
failure and sixteen rejected zero-block draws (`ProverCommitEntropy18.os_error`,
`zero_draws`, `ProverCommitEntropyJoin18.failure_mass_le_bad`). No OS law,
OS-failure numerical bound, zero-mass claim, or durable reservation proof is
supplied in this continuation. The canonical model-statement image and the
shipped `Public::public_bytes = Ok(pubBytes x)` theorem remain obligations;
no error value was invented and no unreachable rejection branch was assumed.

D143 fixes the observable to public statement bytes, submitted proof bytes,
and answers to the adversary's own oracle queries. Programming tables, counts
and timings are internal under that contract. **Timing and other side channels
are outside the privacy contract.** This continuation records that scope; it
does not claim the missing observer-factorization/FSExperiments proof.

No full frozen formal manifest was replayed because its source-refinement
preflight is not green. No unchanged adversarial/runtime/reproducible-build
suite was repeated. The required three frozen SBF rebuilds were performed
once and compare byte-identical. Final focused proof source/hash/axioms audits
pass. All job processes in this job's host directory have finished; pinned
sources and caches are retained. No local target directory was created, no
wallet/key was created or deleted, no other worktree was changed, and nothing
was pushed or merged. `branch-commits.txt` records branch history through proof checkpoint `3384569ae`.

**Target not yet established.** Stop at the demonstrated native ordered-map
transition verification obstruction rather than composing an assumed owner.
