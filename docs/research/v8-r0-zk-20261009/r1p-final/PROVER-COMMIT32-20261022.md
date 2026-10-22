# Prover commitment continuation 32

Base: 26b922be6. Branch: codex/cx-prover-commit32-20261022.
Work in progress. Target not yet established.

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
| AspisR1IndexInsert32.Types | 9021 | see receipt | see receipt |
| AspisR1IndexInsert32.Funs | 9022 | see receipt | see receipt |
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
the theorem's quantifiers. Its receipt is pending at this checkpoint.
