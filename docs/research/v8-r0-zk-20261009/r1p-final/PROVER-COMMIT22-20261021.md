# Prover commitment part 22

Base `d9865ba52`; branch `codex/cx-prover-commit22-20261021`.

Work in progress. Target not yet established; the deployed theorem remains conditional on explicit source refinement.

## Scope

D131 authorizes a fixed model fuel and an explicit exhaustion charge.
The shipped `Coins::nonzero` tests a 32-byte hash answer against all zero,
not an M31 field element. Its uniform-answer zero mass is 2^-256; the
requested M31 reciprocal is a conservative upper bound, subject to fresh
oracle addresses and the ROM transport. Three calls per attempt, eight
attempts give at most 24 instances. Model fuel will be five draws.

## Stage 1 — fixed fuel and conditional deployed endpoint

`ProverCommitFuel22.agrees` proves by induction on the shipped-shaped
successful-run relation that every terminating run of at most k draws has
the same answer and final counter in the fuel model. `stable` proves that
additional fuel cannot alter a successful result. The actual extracted
coin step is used, with failure/divergence preserved by `search`.
J8748/J8749/J8751 are excluded elaboration failures; J8752 passes
(exit 0, 1.81 s, 4041344 KiB, zero swap).

`nonzero-five-v1` Kani passes the actual shipped `Coins::nonzero` with a
symbolic prefix of zero through four zero answers and any nonzero final
answer. It checks every concatenation frame, ordered counter, retained
state, returned answer and exact number of draws; start has room for five
increments. Exit 0, 24.723 s, 833372 KiB, zero swap. This is a universal
bounded successful-prefix check, not a termination argument for HOST_HASH.
The existing per-draw coin transition/extraction is reused.

`ProverCommitFuelMass22` proves the exact independent-coordinate
exhaustion mass, finite union charge, old-event containment, augmented-event
mass and revised numerical bound. With k = 5 and 24 instances,
charge = 24 / 2147483647^5 ≤ 2^-120 per side. The actual uniform 256-bit
answer mass is smaller; `ProverCommitFuelJoin22.failure_mass` proves this
symbolically from answer cardinality. No large universe is enumerated.
J8750 is excluded; J8753 passes (2.08 s, 4059696 KiB).

`ProverCommitFuelJoin22` retains an independent fuel-coordinate tape in
its coupling, fixes the additional event to all-zero blocks on that tape,
and bounds observable-test transport with the extra charge. `of_seed`
extends an old seed coupling without altering either output marginal.
J8754/J8755 are excluded, J8756 focused and J8757 final pass
(2.11 s, 4060524 KiB). All recorded Lean axioms are subsets of
[propext, Classical.choice, Quot.sound], zero swap.

`ProverCommitDeployedFuel22.privacy_headline_deployed` proves the same
privacy game conclusion with enlarged fixed events, total error increased
by 2·charge, and still strictly < 2^-100. J8758 passes (12.37 s,
4204148 KiB, zero swap). `seed_refinement_implies` proves the old deployed
premise implies the new one. This is a genuine implication after adding
retained independent coordinates; it is not a source instance.

The remaining source coupling must identify the per-instance retained fuel
coordinates with successive fresh shared-oracle requests, including adaptive
start counters. Marginal coordinate uniformity alone is not that join.
Neither this packet nor the new endpoint asserts the join is proved.


## Stage 2 — universal Lean Std.TreeMap transport

`ProverCommitTreeMap22` proves arbitrary-tree lookup/enumeration graph
agreement with the existing first-match list model, insert/overwrite lookup,
sticky collision agreement, and composition over arbitrary finite write
schedules with repeated keys. Enumeration is ordered under the supplied
lawful comparator. These are universal **Lean Std** model theorems. They
place no tree-height, key-length, prefix-length or cardinality restriction.
J8759 is excluded; J8760 focused passes; J8761 is an excluded Boolean
precedence elaboration failure; changed-source J8762 passes (exit 0,
1.27 s, 2530276 KiB, zero swap, standard axioms only).

The direct Rust operation gate `tree-insert-get-v1` uses the exact shipped
`BTreeMap<Vec<u8>,[u8;32]>`, one preexisting entry, symbolic one-byte keys,
arbitrary 32-byte answers and a symbolic queried key. It tests the returned
previous answer, lookup and size. Even this shape reaches the 6 GiB region:
stopped for representation/formula review at 6442090496 cgroup bytes,
exit 1, 343.417 s, peak process RSS 6270156 KiB, zero swap.
`tree-insert-stop.json` records the exact terminated process and scope.
No counterexample and no successful per-operation source certificate are
claimed. No unchanged larger-cap rerun is performed. The unrun enumeration
harness is retained as a proposed gate, not evidence.

The missing obligation is the Rust std library representation relation.
An arbitrary Lean tree theorem plus bounded node fixtures does not prove
that relation. No program/source equality is installed from this check.


## Stage 3 — concrete sampler reuse; TLS obstruction

`ProverCommitSemanticSampler22` reuses the soundness-side semantic sampler
proof from `lean/bridge-selected-current-20261018/ExtractedSourceSemanticSampler.lean`.
It removes the unrelated large first-25 caller import, uses the exact cached
QM31 sampler and SqueezeOracleBridge, and proves the same canonical four-digit
decode and fixed exact-tower embedding. `sample_total_semChal` obtains the
successful sampled value itself, rather than assuming source success.
J8763 is excluded; J8764 focused and J8767 final pass (exit 0, 1.94 s,
3959336 KiB, zero swap).

`ProverCommitCircleSampler22` reuses `R4TransportCircleCoordinates` with that
sampler bridge. `circle_total_coordinates` covers every input block and
both circle rows, including both fallback points. J8769 passes (exit 0,
2.14 s, 3974604 KiB, zero swap). All new sampler/circle theorem audits use
only standard axioms. This proves concrete sampler outputs, not reachability
of the simulator's rows or a complete continuation join.

`r4-reuse-binding.json` confirms the shipped sampler.rs and
r0_transcript.rs files are byte-identical to the R4 source-inventory pins.
The exact proof-port diffs are retained. The initial source-graph inventory
was insufficient because it encountered legacy/current source variants.
A separate metadata utility read 1825 retained module headers, without
importing their declarations, and determined the precise circle dependency
closure. J8765 is an excluded utility elaboration failure; J8766/J8768 pass
(metadata only, no mathematical theorem). Forty missing retained objects
were copied into Env J; **zero existing source files or objects were
overwritten**. Exact SHA-256/size/import/sidecar pins are in
`r4-installed-closure.json`. No object or binary is committed.

The actual native TLS gate `tls-append-v1` fails because Kani reaches
`pthread_key_create` in std::sys::thread_local::key::unix::create, an
unsupported foreign call. Exit 1, 4.612 s, 547548 KiB, zero swap. Remaining
pointer/assertion failures after that unsupported operation are not accepted
as Rust counterexamples. The original gate and complete logs are retained;
no TLS stub, axiom, or assumed native-to-owned trace equation is installed.

The existing part-21 success and rejection fixtures are reused unchanged;
they compare complete ordered request/answer histories and serialized native
traces, but remain fixtures. Gamma/ordinary/query optimized-shell and caller
reachability joins from R4 remain explicit, as does native TLS refinement.


## Endpoint audit and demonstrated stopping conditions

`shippedProverExperiment` and its two WholeRunJoins are **not constructed**.
The explicit Rust refinement is retained. The new endpoint enlarges the
fixed bad event and error allowance; it does not discharge or hide the
source obligation and does not narrow the Rust source residual.

The demonstrated blockers are the direct BTreeMap source-gate formula
pressure near MemoryHigh and reachable unsupported native TLS. The
remaining deliverables are a universal source/library representation join,
concrete remaining sampler-policy/row/caller/error/retry assembly, and the
adaptive shared-oracle fuel-tape/history adapter, before either WholeRunJoin
can be honestly constructed. No proof of the model compared with itself is
substituted for a source instance.


## Stage 1 endpoint statements — verbatim

Before (`PrivacyR1HeadlineDeployed`):

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

After (`ProverCommitDeployedFuel22`):

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
