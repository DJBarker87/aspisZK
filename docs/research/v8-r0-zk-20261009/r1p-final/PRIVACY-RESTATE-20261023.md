# Privacy endpoint against the mathematical ideal, 2026-10-23

Branch `codex/cx-priv-restate-20261023`. **The new conditional endpoint is
proved; concrete deployed privacy remains conditional on the real run join.**
Read LOG D184–D185, the root Security and proof discipline rules (especially
section 3), and the common worker/build instructions. D185 explicitly resolves
the earlier stop: the comparison contract is the ideal game with mathematical
`simE`. The prior audit and stop remain in commits `0ddade8ebd` and
`4528e0f9eb` (the obligation-map commit).
No equivalence of the two fixed ideal experiments is asserted.

## Established claim and contract choice

Added only `lean/R1Z/PrivacyR1HeadlineDeployedReal.lean`:
`R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`.
Its only refinement premise is `RustRealRefinement`, definitionally the first
conjunct of `ProverCommitDeployedFuel22.RustProverRefinement`. It compares
`rust.real` observed by `rust.observe` with `source.ideal(simE)` under the
mapped ordered observer. Both existing endpoint modules, all their definitions
and the old theorems are unchanged. No Rust, protocol, event definition or
release artifact is changed.

The theorem uses the existing `ProverCommitModelCore16.core_privacy` through
`ProverCommitReencode16.privacy_transport` for source.real ≈ source.ideal.
The real `ProverCommitFuelJoin22.test_bound` supplies the other edge.
For every adversary and every valid honest witness, triangle inequality gives

```text
|R_rust - I_source| ≤ modelError + lazyBudget(8*n1)
                     + 8/2^486 + seedBudget(2^64) + fuelCharge.
```

The proof then pads by the nonnegative already-charged ideal-side allowance
`8/2^486 + seedBudget(2^64) + fuelCharge`, and uses the existing lazy-to-fresh
bound. The exported envelope is **exactly** the old one:

```text
E = modelError W Pr L₁ L₂ + 16/2^486 + freshBudget(8*n1 W Pr+1)
    + 2*seedBudget(2^64) + 2*fuelCharge
E ≤ 1/2^109 + 1/2^137 + 1/2^454 + freshBudget(8*n1 W Pr+1)
    + 2*seedBudget(2^64) + 2*fuelCharge
E < 1/2^100.
```

No bad-event term is added, replaced, or implicitly assumed zero. Keeping the
unused ideal allowance is deliberate: it preserves the exact headline budget.

## What “old + conjunct 2 implies new” means precisely

In the old proof contract, the refinement certificate is `C1 ∧ C2`.
The compiled theorem `old_refinement_implies` proves
`(C1 ∧ C2) → RustRealRefinement` by the term `old.1`.
Applying the compiled new headline then proves
`(C1 ∧ C2) → NewHeadline(E)`. Consequently every valid instance of the old
two-join theorem also has the new headline at exactly E; there is no added
requirement. This is the precise certificate-level implication implementing
D185's “old + conjunct 2 implies new”. In fact C2 is unused in this derivation.
It does not certify the native Rust simulator, nor discharge C1 for Rust.

Distinguish that implication from a claim about isolated probability bounds.
Writing `OldBound(E) := |R_rust-I_rust| ≤ E`, C2 is an **except-bad** join,
not exact equality: it yields `|I_rust-I_source| ≤ δ_ideal`, where
`δ_ideal = 8/2^486 + seedBudget(2^64) + fuelCharge` after the existing mass
bounds. `OldBound(E)` plus that inequality alone gives `NewBound(E+δ_ideal)`,
not a same-E implication. The same-E result above is proved from the retained
C1 and the model theorem, avoiding double-charging. No same-E biconditional
between the raw old and new conclusions is claimed. Conversely, the new
headline alone cannot establish any property of arbitrary `rust.ideal`.
The earlier fixed-experiment counterexample remains valid; D185 chooses the
mathematical benchmark rather than overturning that observation.

## Quantifiers, observations, error and simulator efficiency

The universal protocol context is unchanged: `CommitHandle`, `Aux`, `template`,
`outputs`, public statement `x`, `rust`, and `observer_program`. The honest
builder is fixed as before. Within the conclusion, **every** `rust.Adversary`
and **every** `w : h.Instance` with `h.public w = x.1` remain quantified.
There is no new statement/witness domain restriction, no fixed fixture, no
restriction of adaptive observer queries, and no `Aux := Unit` specialization.

The real observable is the same full `ROMView` and Boolean observer decision;
the join demands their equality outside the same fixed realBad, seed-guess
and five-draw fuel events. It does not merely identify acceptance or roots.
`RomObserverBin.observerMap` retains `rust.observe adv` and the supplied
adaptive query program. Ordered history, duplicate queries, answers, retries,
errors and aborts must still be represented by the real join. D143's deployed
projection publishes statement/proof bytes and the adversary's oracle answers;
internal tables/audit counters are not publication. L1/L2 side-channel
transport remains a separate open obligation, not proved here.

What changes: the right experiment is source.ideal instead of rust.ideal;
its random carrier is source.IdealRand instead of rust.IdealRand; its observer
is interpreted through the existing map; the native ideal join C2 disappears.
The new headline needs no Fintype/Nonempty instances for rust.IdealRand.
The real Fintype/Nonempty context stays (Lean warns Nonempty is unused).
The old ideal-carrier instances occur only in the separate compatibility
projection lemma. E, the displayed numeric bound, and the `< 2^-100` target
are identical. The deployed real observation has not changed. Thus this
establishes the D185 simulation contract about deployed outputs, while the
old fixed-experiment theorem additionally compares a native ideal implementation.

Efficiency now concerns the mathematical simulator and ideal-game computation.
Reuse the SIM-COST results for that computation: `SimCostIdeal.run_erase`,
`SimCostRelativeIdeal.run_relative`, the primitive/representation bounds of
passes 5–6, and `SimCostOuterRetry6.scan_firstGood`/`eight_bound` (8*C+17).
These are proved cost results for the mathematical computation with their
stated preparation/decision and size hypotheses; no native sim.rs binding is
needed for the new privacy inequality. The headline itself is a probability
statement and adds no cost premise. Do not promote the existing relative cost
results to an unconditional numerical efficiency certificate for arbitrary
callbacks: D142–D143 and SIM-COST7 still require the concrete public/metadata
instance, exact Boolean P_R1 cost, representation/preparation composition and
numeric C. This work neither proves those obligations nor changes simE.

## Verbatim before and after statements

These declaration headers are extracted verbatim from the actual old and new
modules. The surrounding notations and instances are in those linked sources;
the snapshots `privacy-restate-20261023/{before,after}.lean.txt` are checked
by `audit.py`. The before statement remains in the repository unchanged.

Before, namespace `R1Z.ProverCommitDeployedFuel22`:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After, namespace `R1Z.PrivacyR1HeadlineDeployedReal`:

```lean
theorem privacy_headline_deployed
    (refinement : RustRealRefinement template outputs x rust observer_program)
 :
    (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
      |mean (realTest h B outputs rust adv x w) -
        mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
          (simE (h).transport B outputs x))| ≤
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

The full refinement definitions (also verbatim):

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
```

After:

```lean
def RustRealRefinement : Prop :=
  ∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))
```

## Stage 2: remaining real-side obligations

This map is a source/report audit, not a replay of the historical receipts.
All part references below are the corresponding `PROVER-COMMIT<n>-<date>.md`
reports in this directory; LOG acceptance entries distinguish completed local
results from the source joins they do not establish.

| Parts | Established local result | Consequence and remaining real-side work |
|---|---|---|
| [27](PROVER-COMMIT27-20261021.md) | Effectful CoinOracle call/sequence, finite 115-word product marginal, complete cursor/recording/collision effects and ordered history; bounded native control checks. | Reuse only where the real caller actually uses the certified operation. Native wrapping/caller bounds and whole source binding must be retained. Returning only a digest loses state. |
| [28](PROVER-COMMIT28-20261022.md) | State-transformer semantic/circle/suffix port; complete constructed walk and reset/history laws. | A constructed continuation is not a native outer-owner or deployed retry theorem. Rejected-prefix history cannot be discarded. |
| [29](PROVER-COMMIT29-20261022.md)–[30](PROVER-COMMIT30-20261022.md) | Semantic rows/validator/callee split, selected-record and counter composition; 25 native caller cases and logged walk. | These principally bind `sim::walk` on prepared records. They do not construct the real masks, perform reservation or publish the real proof. Apply shared helper equations only after checking source identities. |
| [31](PROVER-COMMIT31-20261022.md)–[32](PROVER-COMMIT32-20261022.md) | Owned simulator publication source checks; recursive ordered-list publication/lookup equations. | Historical extraction/collection obstructions; neither result supplies a real prover publication certificate. Use D144 structural owners and D145 TrustedStd, not another full iterator extraction or BTreeMap-internals gate. |
| [33](PROVER-COMMIT33-20261022.md) | Lazy entry, folded-loop, query-answer and ordered merge transport; source-image counterexamples. | Install a concrete statement/public-byte/observable projection on D146's representable domain. WideExact fields and unbounded Nat indices cannot all be mapped field-preservingly to Rust M31/u64. This is a visible domain specialization, not part of dropping conjunct 2. |
| [34](PROVER-COMMIT34-20261022.md) | DeployedStatement/public-byte law, structural eight-attempt owner, OS/zero failures distinguished. | Bind this owner to the actual S2 feature-selected caller; an arbitrary `next_attempt` callback does not guarantee successful-draw law E1 or correct mask construction. |
| [35](PROVER-COMMIT35-20261022.md)–[36](PROVER-COMMIT36-20261022.md) | Byte-blind faults, fail-closed/replay, reservation retention/extracted bridge; faithful ledger and conditional bounds. | Preserve arbitrary schedules and private ledger state, atomic E2 and E1 successful draws. No error-free OS premise, failure-probability shortcut or implicit ledger cap. E1/E2 alone do not imply a hash address law. |
| [37](PROVER-COMMIT37-20261022.md)–[38](PROVER-COMMIT38-20261022.md) | ROM coordinate/memo analysis and explicit reservation event; saturated-ledger counterexample to a small universal ledger-hit charge. | Retain as corrections/evidence. Do not charge adversary ledger size or revive the uniform-secret-nonce premise for the selected public-nonce route. |
| [39](PROVER-COMMIT39-20261022.md) | Shared-ledger prefix coupling; source nonce-ownership finding. | Use public proof-account nonce, chosen by the adversary even after earlier queries; duplicate/fault outcomes couple exactly before witness-dependent work. Native source-to-experiment and successful continuation remain to compose. |
| [40](PROVER-COMMIT40-20261022.md) | Private raw-seed memo counts, public-nonce model, hash-family classification and conditional numeric envelope. | Both private OS seeds need the actual adaptive law. The extra `4*Q*attempts/2^256 + 16*(3/2^256)` envelope is proved conditionally, **not installed** in the current headline. Do not claim the current fixed realBad/seed/fuel join already contains it. |
| [41](PROVER-COMMIT41-20261022.md) | Conditional ROM law retaining public-prefix answers, duplicates, adaptive histories; public binding and mixed-read agreement. | Instantiate the actual real commitment continuation; public precommit/attempt binding answers may already be queried. Treating them as fresh has probability-one counterexamples. |
| [42](PROVER-COMMIT42-20261022.md) | Concrete normalized private-read bounds and honest run agreement; generated 64-byte entropy owner/model/ledger/retry bridge. | Local statements retain RCommitBytes, ROpen, RComLog; global run retains RAddrIn, RCausal, public memo coherence and bad complements. Joint adaptive reservation/oracle histories and the complete native successful continuation are not closed. |
| [43](PROVER-COMMIT43-20261022.md) | Native full-byte candidate transition plus sixteen-step Lean induction, closing part 42's native entropy-loop obstruction; ordered publication/leaf/padding helpers. | Consume the selected 64-byte callback, including OS payloads and zero exhaustion, in the real retry owner. Publication helpers largely concern simulator-specific synthetic trees; establish the corresponding native real Merkle/encoding path separately. |
| [44](PROVER-COMMIT44-20261022.md) | Ordered parent set and native parent transition through 18 levels; length-interface countermodel. | Preserve salt/coin order and root guards where the caller matches. Native simulator tree equivalence does not identify real committed trees or proof serialization. |
| [45](PROVER-COMMIT45-20261022.md) | TrustedStd length/sort/dedup fields, guarded tree/transcript finalization; ProgramOne effect-gap countermodel. | `ProgramOne` is a simulator callback. Its unresolved RefCell effect is not automatically a remaining obligation for a real-only headline; neither can a digest-only callback justify real state changes. Parts 46–55's native simulator binding is explicitly stopped by D184. |

### Concrete real owner and publication deliverable

The selected source path is
`generate_for_mask_nonce` → `prove_masked_retrying_with` →
`prove_masked_attempt` → `prove_masked_with_attempt` →
`host_semantic::build_with_material` → `prove_from_semantics`.
Actual files: `crates/aspis-prover/src/state_only_entropy.rs` and
`crates/aspis-r1-cost-probe/src/prover.rs`. The wrapper at prover.rs:327
uses the different 96-byte `generate()` API; it is not the selected deployed
proof-account route. At prover.rs:354 the generic callback is invoked
before each attempt; only `Error::Rejected` continues. Every other error
aborts; only successful proof/audit returns; eight rejections exhaust.
The comments' freshness assertions are not proofs of the arbitrary callback.

The next concrete real deliverable should compose the selected 64-byte owner
and reservation bridge into that actual callback and loop, then bind the
successful mask/builder/commitment/semantic/checker/serialization path.
Retain the same public nonce and environment schedule in both worlds,
reservation before the first witness-dependent trace use, nonzero candidate
selection and all error exits. Establish that the successful source proof
bytes equal the model's reencoded observation, including phase-indexed roots,
semantic messages, openings and verifier/adversary ordered query answers.
Transport the observer's complete decision and adaptive queries, not only
acceptance, a root or a successful fixture. Prove the D143 projection removes
internal audit/timing/attempt/programming data from publication; local function
return values alone do not establish deployment visibility.

Then construct the concrete real experiment, its exact random marginal,
and `ProverCommitFuelJoin22.RunJoin` outside the **specified** realBad plus
seed/fuel predicates. Those predicates are fixed, not implementation-chosen.
The current source/entropy analysis introduces private-memo and zero events
not yet visibly composed into that endpoint. Either prove their containment
with valid mass accounting in the existing event carrier, or explicitly
report the changed real contract/envelope. Do not silently add exceptions or
pretend that the conditional part-40 arithmetic is a completed join.
A generic coupling hypothesis would merely restate this remaining work.
The retained premise is meaningful and model-satisfiable (an identical real
model admits an identity coupling and independent seed/tape extension); this
does not supply the missing shipped instance or assume the security conclusion.

### Candidate v2 differences and adoption

Read-only comparison is pinned to candidate
`b2f95e269a` (`codex/cx-ct-kernels-v2-20261022`), as in D172.
`privacy-restate-20261023/candidate-audit.json` records its full revision,
merge base, relevant changed files and source hashes. This branch has not
been checked out, modified, merged or adopted here.

| Changed path | Required refinement/adoption consequence |
|---|---|
| `aspis-core/src/field/{ct.rs,wide_exact.rs}` and `field.rs` | Constant-time kernels need their recorded arithmetic equivalence composed at each real caller; local Kani kernel checks alone are not the whole real-experiment join. |
| `host_semantic.rs`, new `ct_pole.rs` | Branch-free equality and eager all-slot pole scan must preserve the exact VR1 rejection law, malformed/error paths and accepted trace. |
| `prover.rs`, `trace.rs`, feature manifests | CT feature gates TLS value/check-time recording off. Rebind source pins/features and observation projection; do not reuse the old recorder/thread premises unchanged. The retry body itself has no candidate diff in the inspected three-dot comparison. |
| P_R1 probe implementation (`z4/z9e.rs` plus `z9c.rs`/`z9d.rs`, and `c3/build`/`c3/check`) | D171–D172: blocked exact M31 arithmetic, deterministic bounded workers and first-lift reuse must preserve all check verdicts, early rejection and panic/error handling. Pin these path dependencies under `docs/research/v8-r0-zk-20261009/`; their changed production sources are included in the candidate audit. |
| `host_sumcheck.rs`, `host_commitment.rs`, new `host_work.rs` | Sixteen public work ranges and deterministic merges change semantic point evaluation/lane encoding callers. Reprove source/model correspondence and joint trace transport; same fixture bytes do not establish equality for every statement/witness/challenge. |

D167/D171/D172 report kernel/control gates, differential challenge checks,
unchanged fixture proof/public bytes and verifier ELF pins. D172 measures
13.63/13.98 s medians on the specified 16-core host; those are measurements,
not universal cost or refinement proofs. Adoption still needs changed-path
native refinement, D166's simulatable joint L1/L2 trace transport, expanded
thread/TLS assumptions and the pinned x86_64 Linux L3 receipt. The discarded
stage-3 fixed-shape rewrite is not v2 and must not be reintroduced as an
obligation or silently attributed to it. These gates remain independent of
whether the never-deployed native simulator is bound to simE.


## Validation and handoff

Stage 1 source commit: `7669f7d878`; stage 2 receipts: `80ff33c16b`.
The final report/audit stage is committed separately. No push or merge.

| Field | Recorded result |
|---|---|
| Exact target | `R1Z/PrivacyR1HeadlineDeployedReal.lean`, including `privacy_headline_deployed` and `old_refinement_implies` |
| Environment/attempt | J10800 (J10801–10899 unused) |
| Source revision | `7669f7d878` (full revision in `attempts.jsonl`) |
| Source SHA-256 | `0374f534aaadcfcf3855dc9402feaae176f93f11687b0fab7773b075599e7b42` |
| Dependency fingerprint | `43ba1775696887d0`; imported source/object pins in `dependencies-10800.json` |
| Exit/wall/peak RSS/swaps | 0 / 12.16 s / 4,319,944 KiB / 0 |
| Cgroup/Lean caps | MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0; Lean -M7000 |
| Host reservation | 24 GiB populated before launch, 31 GiB including this job, below 55 GiB |
| Axioms, both added theorems | `[propext, Classical.choice, Quot.sound]` |

Complete axiom lines and warnings are retained in
`privacy-restate-20261023/out-10800.log`; resource receipt in `time-10800.log`;
normalized machine-readable result in `attempts.jsonl`. Both new theorems
were audited in that single compile. Warnings are an unevaluated large
exponent and unused Nonempty section instances; no limits were raised.
No failed real compile, unchanged rerun, generated certificate, or cold build.
The private launcher changes only the authorized attempt range from the
existing launcher. Added one previously absent module/source/object to the
shared J tree; no existing shared source/object was overwritten. Its sole
direct imported source matches the repository SHA-256 exactly.

`audit.py` checks the unchanged old endpoints against the historical pins,
the exact before/after excerpts, identical numeric envelopes, the real-only
proof references, and the compiled source hash/standard axiom receipt.
`source-audit.json` records the current read-only source pins.
`candidate-audit.json` is the retained read-only candidate inventory, not a new
candidate verification. `git diff --check` passes. No existing Lean module,
`crates/`, `programs/`, wallet or key changed.

Validation is the focused new module against cached J dependencies, not a
fresh coherent release-closure replay. Historical parts 27–45 and SIM-COST
receipts are reused as cited evidence, not rerun; no Rust or SBF build was
needed for this theorem-only change. No full frozen manifest was replayed.
A final release still needs its coherent closure/artifact evidence.

Stopped after the requested endpoint, compatibility projection, verbatim
statement audit and obligation map. **Target not yet established for a
concrete deployed Rust instance:** construct C1 by composing the selected
64-byte entropy/reservation owner and actual `prove_masked_retrying_with`,
then the successful builder/checker/prover/publication and complete adaptive
observation transport, accounting for the unresolved events above. Candidate
v2 adoption and joint L1/L2 side-channel transport remain separate gates.
Native simulator binding is no longer on the critical path under D185.
