# Privacy endpoint restatement audit, 2026-10-23

Branch `codex/cx-priv-restate-20261023`; inspected revision
`235da438aa136271c0380b2f8f2acf57203ea032`. **Stopped on item 2's equivalence
condition; target not yet established.** No new endpoint is claimed proved.
Read the binding AGENTS.md security/proof rules, common worker rules,
LOG D42–D68 and D184, and the actual endpoint definitions.

## Stage 1: conclusion audit and explicit stop

D184 correctly identifies a sufficient route to the standard simulation
claim: couple deployed real execution to model real execution, then use the
proved model comparison to the mathematical ideal simulator. Native
`sim.rs` correspondence is unnecessary for that new comparison. However,
this is a different theorem from the current **fixed-experiment** conclusion.
The requested equivalence cannot be asserted for its actual quantifiers.
This finding does not invalidate privacy of the deployed prover.

`FSExperiments` independently supplies `real`, `ideal`, and `observe`.
`ZK_FSS` does not existentially quantify over an ideal implementation and does
not identify it with the mathematical game. Its conclusion expands to:

```lean
∀ (adv : rust.Adversary) (w : h.Instance), h.public w = x.1 →
  |mean (realTest h B outputs rust adv x w) -
    mean (idealTestS rust adv x (simE h.transport B outputs x))| ≤ ε
```

The proposed comparison instead is (explanatory notation, **not an added
or compiled declaration**):

```lean
∀ (adv : rust.Adversary) (w : h.Instance), h.public w = x.1 →
  |mean (realTest h B outputs rust adv x w) -
    mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv)
      x (simE h.transport B outputs x))| ≤ ε
```

Let the three means be R, I_rust, and I_source. The old conclusion says
`|R - I_rust| ≤ ε`; the proposed conclusion says `|R - I_source| ≤ ε`.
Holding every real-side field fixed and changing only `rust.ideal` leaves
the proposed proposition, model theorem, and conjunct 1 unchanged, but can
change the old proposition. At the scalar level, R = I_source = 0 and
I_rust = 1 satisfy the proposed bound and violate the old one for ε < 1.
These are legitimate Boolean experiment probabilities. The FSExperiments
interface imposes no law preventing the ideal field from ignoring its
simulator argument. This is a counterexample to a general equivalence
argument, not a constructed attack on the selected model or a claim that
its concrete distribution has those particular means.

The current second join bounds the missing `|I_rust - I_source|` term;
it does not give exact equality either. Removing it while retaining the
same old conclusion is unsupported. A triangle inequality with nonzero
ideal discrepancy is not a same-ε biconditional. Changing only the benchmark
is a valid way to state the intended deployed simulation property, but is
not a literal premise removal from the existing theorem. Under the explicit
instruction to stop if the conclusions are not equivalent, no new Lean
module, wrapper, or compile is submitted. Recommendation to the lead:
explicitly approve a **different composed simulation theorem** with the
mathematical ideal as its fixed benchmark, retaining the old theorem as-is.
That needs no deployed native Rust simulator. It does not require weakening
the adversary or security target.

## Quantifiers, observations, error and efficiency

The existing declaration is universal over `CommitHandle`, `Aux`, `template`,
`outputs`, public `x`, `rust`, and `observer_program`; internally over every
`adv` and every honest instance `w` with `h.public w = x.1`. It uses the
fixed admitted builder. The proposed comparison need not change any of
those quantifiers. In particular it must not silently install the D146
source-representable statement domain or identify arbitrary `Aux` metadata
with unit. Neither concrete deployed instance nor real join is supplied.

The real observable stays the entire ROMView and Boolean decision. The
observer map keeps `rust.observe adv` as its decision function; its adaptive
query program is supplied by `observer_program`. The model retains its
existing query fuel, query order, repeats, early exits and oracle answers.
The ideal random carrier changes from `rust.IdealRand` to
`source.IdealRand`; the ideal experiment and source observer interpretation
change accordingly. A real-only endpoint should not need finite/nonempty
instances for `rust.IdealRand`. Those are real changes to the statement,
even though the deployed real observation is untouched.

The current fuel endpoint's exact envelope is
`modelError W Pr L₁ L₂ + 16/2^486 + freshBudget (8*n1 W Pr+1)
 + 2*seedBudget (2^64) + 2*fuelCharge`.
Its conclusion also gives the displayed numeric upper bound and `< 2^-100`.
A one-join triangle uses only the real mass, seed and fuel charges, so it
could conservatively retain this entire envelope without new charges.
This arithmetic sufficiency does not prove equivalence of the benchmarks.
The old seed-only endpoint omits the two fuel charges and has the same
benchmark issue. The exact fuel statement is reproduced below.

Efficiency of the new benchmark would concern mathematical simE **and its
whole ideal game**, not whether the never-deployed Rust cost probe matches
it. The cost passes prove conditional run equality/relative bounds; the
latest `SIM-COST7-20261022.md` expressly leaves concrete public/metadata
selection, exact Boolean P_R1, full representation costs and a numeric
preparation certificate open. It would be inaccurate to report an
unconditional concrete simE cost bound as established. No such assumption
is discharged or added by changing the benchmark.

## Verbatim before and retained after

Both snapshots are extracted from
`lean/R1Z/ProverCommitDeployedFuel22.lean`, with the module's unchanged
surrounding variables and local notations. They are verbatim declaration
headers, excluding proof bodies. `privacy-restate-20261023/audit.py` checks
them against the actual source; the retained after is identical because the
stop condition prevents installing the proposed different conclusion.

Before:

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

After (retained unchanged; no new endpoint):

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

`python3 .../privacy-restate-20261023/audit.py` passes the endpoint/source
assertions; the checked source SHA-256/size pins are in `source-audit.json`.
`candidate-audit.json` is read-only git evidence, not candidate verification.
`git diff --check` passes. Before/after endpoint snapshots match byte for byte.
Historical proof/build/axioms evidence is referenced, not rerun or promoted
to validation of a new theorem.

No Lean or Rust compiler ran; assigned J10800–10899 are unconsumed. No new
theorem, axiom, cost certificate, runtime claim, source join or formal release
result: target/exit/wall/RSS/swap/axioms for a new formal build are all not
applicable. No full regression/manifest, local dependency build, ELF rebuild
or shared host source/object change occurred. All existing `.lean`, `crates/`
and `programs/` sources are untouched. No wallet/key operation, push or merge.

Stage 1 commit: `0ddade8ebd` (statement audit and stop). Stage 2 commits this
independent obligation map and read-only candidate/source evidence. Exact
claim established: the requested raw conclusion equivalence is unsupported
by the FS interface; the standard real-to-mathematical-ideal simulation
route is sufficient but is a different fixed-experiment proposition.
No refinement premise is discharged. Next lead deliverable: decide explicitly
whether to replace the literal equivalence requirement with that simulation
contract, and then prove the new two-edge composition without claiming it
recovers `ZK_FSS ... rust` absent a relation to `rust.ideal`.
