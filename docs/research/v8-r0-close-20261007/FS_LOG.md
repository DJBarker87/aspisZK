# R0 remaining-premise audit — 2026-10-07

## Scope and starting revision

Worktree `/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922`,
branch `research/v8-wide-reference-20261005`, fetched and fast-forward checked:
`810eabd4ce3482ae9d3725d726dc953e2a51ca7b` (already current).
Pre-existing untracked files were left alone. All repository writes are under
this directory. FS/FS2/R0FS and the specifications are fixed interfaces.

## Sampling rule (recorded before proof work)

**Proposed design for the lead, not an existing Wide sampler.** Let
`P = 2^31 - 1`, `N = P^8`, `B = 2^248`. Read the eight little-endian words of
one `SourceDuplexStep.State` using `SamplerWords.word`, and mask each to 31
bits using `SamplerWords.masked`. Decode the first/last four canonical limbs
by `SamplerFieldDecode.decode4` (R601's decoder), into the real/imaginary
QM31 coordinates of `WideExact` respectively. Accept only if all eight limbs
are strictly below P. This agrees with the successful eight-limb path of a
natural extension of the tree's sampler. It does NOT implement the tree's
bounded multi-block retries.

* Round 0: use the decoded value if accepted and nonzero; otherwise return
  `.field 1` (documented default, including zero).
* Rounds 1–3: use the decoded value if accepted; otherwise `.field 0`.
* Round 4: run the tree's q22 scan on the one block's eight masked 18-bit
  words; use the resulting set only if its cardinality is 22, otherwise use
  the fixed legal query enumerating 0,...,21. A single block has only eight
  candidates, so this truncation always defaults. R417's `LegalQuery` is an
  **ordered injection** `Fin 22 → Fin (2^18)`; the challenge uses its image.
* Other round indices return `.field 0`, making sigma total.

Every masked eight-limb tuple has 256 byte-state preimages, hence probability
1/B. The proposed gamma sampler's default atom has exact mass
`1 - (N-2)/B`; every other nonzero atom has mass `1/B`; zero has mass zero.
Its excess over `1/(N-1)` is exactly
`(1-(N-1)/B)*(1-1/(N-1)) > 0`. Ordinary field default mass is
`1-(N-1)/B`, with excess `(1-N/B)*(1-1/N)`. These formulas are mathematical
counting, not yet claimed as Lean theorems about the byte decoder.

**First stop (A2):** even an optimally balanced total one-block sampler cannot
meet round 0. Exact upper bounds on all N-1 possible outputs sum to 1, so
all fibers must have size `2^256/(N-1)`. But 3 divides N-1 and does not divide
2^256. We will prove this obstruction, not assert `samplerLawsD` or advance
to A3. Definitions of the other requested rounds do not claim their laws.

## SEM inventory and statement-only design boundary

No R0 semantic verifier, payment-witness relation, challenge schedule or
semantic failure classifier is defined under `lean/R0/`. `Opening.Data`
contains words, chord points/values, three points and 87 claims;
`Opening.Accept` takes `semantic : Prop`. `R0FS.Witness` means list membership,
point compatibility and subfield descent, **not** a valid payment witness.
Thus even proving that existing extractor succeeds would not prove SEM.

B2 is an **open specification**, not a replacement premise or a concrete
protocol instance. Its semantic-message type, semantic bad-event classifier,
actual payment relation, decision, and projection to the existing opening
prefix must be supplied by a future source formalisation. None has a proof
field. The semantic challenges are K scalars; arbitrary many semantic rounds
are retained so adaptive messages are not collapsed into one sampled tuple.
Each semantic position has the requested conservative budget 396430/(|K|-1),
whose per-prefix bound remains an unproved goal (the V7 aggregate inventory
alone does not imply it). Two following rounds explicitly carry z0, y0, z1;
the five opening budgets reuse `R0FS.ε`. Existing FS2.D1/D2/D3 are applied,
not redefined. This specification cannot instantiate the fixed five-round
`R0FS.V2.rb2` or change the meaning of its extractor.

R0_SOUNDNESS §2 specifies z over **K**, not E. `BaseRational` means both
coordinates in Fp, not membership in the size-2^20 evaluation domain. The
base circle has exactly P+1 = 2^31 points. Intended ideal uniform-circle
rows: `2^31/|Point K|` and `(2^31+1)/|Point K|`; equality holds in the second
numerator when z0 is non-rational. These count bounds require a sampler-law
bridge before they are FS2.D2 statements on squeezed bytes.

### Retained step-3 source rule (before its additional proofs)

Further source inspection found `SamplerCirclePolicy`, `DistinctCircleProgram`
and `CirclePairPrefixProgram`: sample a QM31 parameter with bounded limb
retries, reject singular parameters and **all CM31 parameters**, with three
outer attempts; after the first point absorb y0, retry an equal second point
(up to three distinctness attempts), then absorb y1. All exhaustion errors
remain errors. Thus successful source-shaped outcomes are stronger than the
ideal full-circle rows: both are non-rational and distinct. They must not be
identified with uniform draws from the full circle or with a total one-block
sigma. We will prove the successful-outcome facts without discarding errors.

## Compiled results and scope

| Source | Proved result |
|---|---|
| `lean/R0C/Counting.lean` | Ideal point-mass upper bounds for a total map between abstract finite types force equality of every mass and divisibility of cardinalities; uniform predicate density equals its subtype cardinality divided by the ambient cardinality; adjoining one point costs at most one atom. |
| `lean/R0C/SamplerObstruction.lean` | `noSamplerLawsD`: for **every** `Duplex.Params (R0FS.Msg WideExact) (R0FS.Chal WideExact) L`, message map, and Sfield, `¬ R0FS.V2.SamplerLawsD p msg`. Uses only `nonzero` and `gamma` of the existing law. |
| `lean/R0C/Sampling.lean` | A1's total proposed sigma; gamma is always nonzero and queries always have cardinality 22. No uniformity claim. |
| `lean/R0C/SemStatement.lean` | Statement-only open extension, compiled and committed ALONE as `7db5a56e7`, before proof files. Semantic operations are unspecified data; `SemanticDensity` and the existing D1/D2/D3 applications are unproved Props. No SEM implementation is invented. |
| `lean/R0C/CircleRows.lean` | `baseRational_card = 2^31`, `z0_density`, `z1_density_le`, and `chord_conditions` supplying exactly distinctness and non-rationality outside the two bad events. |
| `lean/R0C/CircleCard.lean` | Symbolic split-circle bijection to nonzero field elements; `qm31_circle_card : Nat.card (Point QM31Exact) = P^4-1`. No concrete circle enumeration. |
| `lean/R0C/CircleSource.lean` | Successful retained circle-policy outcomes are non-rational; `distinct_success_conditions` proves the retained bounded second-point run returns a non-rational point unequal to the first. Errors remain visible. |

All final theorem audits use only `propext`, `Classical.choice`, `Quot.sound`,
with the small numeral divisibility lemma using only `propext`.
No new axioms, incomplete proofs, native decision procedure or resource-limit
options appear in the final Lean sources. The proof of impossibility is
independent of the proposed sampling design and its unformalised bias arithmetic.

The requested A2 stop was reached at gamma. Consequently A3 was not attempted;
there is no honest `samplerLawsD` or hypothesis-free specialization of
`R0FS.V2.r0_duplex_fiat_shamir` for WideExact. The existing conditional theorem
is not disproved; its sampler premise has no instance at these fixed types.

## B1 — semantic theorem inventory

Inventory searched the current `AspisFormal/AspisFormal`, the V8 research Lean
roots, all R0/R0FS sources, and every Lean occurrence of `396430`. Paths below
are relative to `AspisFormal/AspisFormal/` unless another root is given.
The list includes the numerical inventory, ideal probability theorems,
production comparison statements and deterministic coverage they actually use.

| File / theorem(s) | Exact relation or experiment; R0 applicability |
|---|---|
| `Pool/V7K15FailureRootInventory`: `fixedFamilyCausalRootCap_sum_eq_396430`, `fixedFamilyCausal_root_inventory_le_two_pow_neg_105` | Sum over V7 `FailureKind`; respectively an integer identity and a real-number inequality. Neither states a semantic acceptance probability for R0. Historical `effectiveRootCap_sum_eq_4078`, `pointCompatibleK14RootCap_sum_eq_3994` and their bit bounds are also arithmetic only. |
| Same file: `canonical_copyChi_branch_card_le_365`, `canonical_activePole_branch_card_le_366`, `canonical_activePole_union_copyChi_card_le_731`, `canonical_tupleCompression_branch_card_le_2928` | Bad sets for `DeployedCopyRegistryProjection QM31Exact producerValue consumerValue` indexed by `RequiredScalarLink`; V7 source registry, not R0.Data. |
| `Pool/V7FixedTupleSemanticSecurity`: `fixedWidth29CombinedIdealSemanticSubtotal_le` | `30500 / card QM31Exact` for `ExactDecoderInstantiation QM31Exact`, `Width29InitialWords QM31Exact`, and terminal/sumcheck plans on `FixedWidth29TupleCandidate decoder lanes`. No R0.Stmt/Data argument. |
| Same file: `selected_semantic_failure_mem_fixedWidth29_family`, `selectedFixedWidth29SemanticSourceOfCausal`, `fixedTerminalAlgebraFailure_implies_bad` | Coverage of `TenRoundRepair` or `FixedTerminalAlgebraFailure` for an `AcceptedProductionTenRoundWire scheme` and a `FixedOracleTenRoundTrace`, with the source's causal message-plan relation. This is not a theorem deriving payment validity from R0's 87 claims. |
| Same file: `production_fixedWidth29SemanticFailureProbability_le`, `fixed_width29_semantic_subtotal_le_two_pow_neg_109` | Production bound has an explicit `ProductionCandidateTerminalConnection` and additive `candidateSelectionHashAndSourceGap`; the latter theorem is arithmetic. No zero-gap R0 connection exists. |
| `Pool/V7FixedC1CopyCollisionSecurity`: `familyLambdaBad_card_le`, `familyChiBad_card_le`, `fixedFamilyCopyCollisionProbability_le_card_mul`, `fixedC1CopyCollisionProbability_le` | Two-stage ideal copy experiment for `PackedDeployedCopySource` over a C1-only family fixed before lambda/chi; final bound `365900 / card QM31Exact`. Related `packedLambdaBad_card_le_2928`, `packedChiBad_card_le_731`, `concrete_lambda_collision_mem_fixedC1_family`, `concrete_chi_collision_mem_fixedC1_family` count/cover that same registry relation. Bit-bound theorem is arithmetic. |
| `Pool/V7K15IndependentRootCertificates`: `independentK15IdealSubtotal_eq`, `independent_k15_subtotal_le_two_pow_neg_119` | `30 / card QM31Exact` from mu-zero, inactive-chi, OOD mix, relation-alpha, kappa-point-row; certificates name those V7 failure predicates. |
| `Pool/V7K15CausalProbabilityClosure`: `causalK15IdealSubtotal_le`, `causal_k15_ideal_subtotal_le_two_pow_neg_105` | Sum of the fixed width-29 family, fixed C1 family and independent subtotal, `396430 / card QM31Exact`. Arguments are decoder, width29Lanes, c1Lanes, terminal, sumcheck, copySource. No R0 relation. |
| `Pool/V7K15FixedFamilyCausalCover`: `failureEvidence_implies_gammaPointLane_or_fixedFamilyK15Failure`, `failureEvidence_implies_fixedFamilyK15Failure` | V7 `V5PublicStatement`, `FixedFieldView QM31Exact`, `AcceptedRun scheme`, `CompactAcceptedRunEvidence`, `CoherentTraceExtraction`, exact terminal plan, causal sumcheck plan; second theorem also requires all point claims exact. Not an R0 semantic classifier. |
| `Pool/V7AcceptedSemanticRelationComposition`: `constraint_rows_vanish_of_compact_acceptance`, `relation_and_point_aggregate_exact_outside_relation_collisions`, `relation_and_point_claims_exact_outside_collisions`, `accepted_semantic_relation_consequence` | Deterministic V7 compact-acceptance consequences for the extracted physical trace and its compiled constraints/copy lane; not a probability bound on R0.Data. |
| `Pool/V7K15FailureProbabilityComposition`: `totalK15Failure_probability_le_branch_sum`, `covered_attack_probability_le_k15_branch_sum` | Generic measure union over V7's thirteen `FailureKind`s, requiring event coverage; does not supply the numerical component bounds. |
| `K1/V7Tag73K15ExactMeasureLedger`: `fixedK15EventBounds_of_ordinary_and_kappa`, `fixed_k15_failure_probability_le`, `covered_fixed_k15_failure_probability_le` | PMF of arbitrary Coins with `FixedK15Events` and **input** `FixedK15EventBounds`; bound `396430/(P^4-1)`. The input has one measure bound per eight V7 categories. The arithmetic weakening/bit theorems do not discharge it. |
| `K1/V7Tag73RestoredK15EventComposition`: `restored_k15_error_measure_bound_of_cover` | `ProofRelevantK12ToK15Stages` on the exact Tag-73 compiler sample, requiring coverage, component bounds and restored-gamma residual bound. Adds an opening residual; not R0 SEM. |
| `K1/V7Tag73ExactRestoredConcreteK16Assembly`: `exact_tag73_restored_concrete_k16_aok_raw_with_all_stage_terms_fixed` | `V5PublicStatement`, `Tag73K12ParsedProof`, `DecodedSpendWitness`, `exactTag73SpendRelation`, retained concrete K13/K14/K15 measure hypotheses. Does not instantiate the R0 relation. |
| `K1/V7Tag73K14K15IdealErrorLedger`, `K1/V7Tag73RestoredCausalErrorLedger` | Remaining `396430` occurrences are stage-sum/ratio/bit arithmetic (including work-normalized V7 bounds), not new R0 semantic theorems. `V7Tag73K15SemanticSequentialRouter` defines V7 SHA slots and their counts, not an R0 acceptance law. |
| `V5SequentialTerminalChallengeBound`: `ThreeStageFreshPlan.failureProbability_le`, `terminalAlgebraFailureProbability_le`, `FixedTerminalAlgebraPlan.{thetaBad_fraction_le,pointBad_fraction_le,muBad_fraction_le}` | Generic fresh three-stage terminal plans with V5 algebraic constraints; 35 roots per fixed trace. No R0 source correspondence. |
| `V5AdaptiveSumcheckChallengeBound`: `adaptiveTenRoundRepairProbability_le`, `productionTenRoundRepairProbability_le`; `V5CombinedTerminalSecurity.combinedIdealTerminalFailureProbability_le` | Adaptive degree-27 ten-round plans, ideal 270-root sumcheck and 305-root combined bounds; production comparison remains explicit. |
| `V5CandidateTerminalSecurity`: `candidateCombinedIdealTerminalSubtotal_le_card_mul`, `_le_240`, `productionCandidateTerminalFailureProbability_le`; `V5PrefixDependentCandidateSecurity`: `prefixAveragedCandidateTerminalSubtotal_le_240`, `_real_le_240`, `productionPrefixDependentTerminalFailureProbability_le` | Arbitrary or prefix-dependent candidate families of terminal/sumcheck plans, with V5 family cap or explicit source/ROM comparison. They do not identify R0's candidate set, payment relation or adaptive transcript. |
| V8 `AspisV8R19/R885CompleteSemanticGridBound.selected_root_grid_bound` | Determinant singularity on a fixed 15-coordinate product grid, degree bound 14049; explicitly no adaptive source/oracle/callback distribution. Not SEM. V8 `R368WireSemanticCompatibility` supplies wire guards; `AspisV8R17/StructuredRound` and `StructuredCube` concern proposed mask algebra, not semantic soundness. |
| R0 `OpeningDefinitions.Accept`, `Binding.binding` / `wideBinding` / `wideProtocolBinding`, R0FS `Witness` | Only opening-layer objects. `semantic : Prop` is supplied to Accept. The extracted tuple satisfies list membership, point claims and subfield descent. No payment relation, SEM bad set, source semantic schedule or R0-stated SEM bound was found. |

The exact stopped implication is:

```
R0 semantic acceptance + t in Lambda(W) + all 87 R0 point claims exact
  -> valid R0 payment witness OR a causal semantic bad challenge
```

The V7 coverage theorem instead consumes its `V5PublicStatement`, compact
accepted wire, coherent extraction, deployed registry/constraint plans and
causality evidence. R0.Data has none of those fields. Merely sharing a field,
29 lanes or the number 87 supplies none of that evidence. No V7-to-R0 bridge
was attempted. This is the B3 stop, not a new assumed proposition.

## Part D — findings and smallest specification/interface changes

### D-A: round-zero SamplerLawsD is false

At `SamplerLaws.nonzero` + `SamplerLaws.gamma`, a total sampler covers the
N-1 nonzero values. Summing its asserted upper bounds forces equality at
every value. `Counting.card_dvd_of_point_mass_le` turns equality of a fiber's
integer count divided by 2^256 into `(N-1) | 2^256`. The compiled contradiction
uses `3 | P^8-1` and `3 ∤ 256^32`. This is a universal obstruction, not just a
bad implementation choice. It is already sufficient to stop A2/A3.

For the documented default rule, the exact gamma excess and total variation
from uniform nonzero sampling are both
`(1-(P^8-1)/2^248)*(1-1/(P^8-1))`, approximately
`3.725290292390382e-9` (28.00000000235 bits). This large bias comes from putting
all rejected blocks into one atom. A balanced one-block encoding improves it
but cannot make it zero: some fiber has at least 257 states, hence some atom
has mass at least `257/2^256`, strictly above `1/(P^8-1)`.
The first formula is the exact bias of the proposed rule; these numerical
bias calculations are ordinary exact integer/rational counting, separately
from the Lean impossibility theorem.

**Smallest changes, not made:** R0_SOUNDNESS §2/§6/§9.9 must specify the actual
sampling and failure rule. Either replace the ideal mass law by the exact
biased pushforward bound and recompute the affected ledger entries, or model
bounded multi-block rejection with an explicit rejecting/error outcome and
prove successful subprobability bounds. For the latter, change the R0 sampler
law's unconditional `nonzero`/`queryCard` requirements to success-branch facts,
and have the verifier reject errors. The existing `Chal` tags could encode
malformed rejection without adding a constructor, but the law and D3 proof
still need a deliberate revision. FS_GENERIC should explicitly describe
subprobability/error treatment and count every retry read in Q_tot.

FS2.Statement.Sampler already permits finite adaptive reads and `multi`;
`FS2.Duplex.Params.σ` / `samp` / completing decoder still restrict this instance
to one squeezed block per round. The latter interface and its decoder proof
would need generalizing to the bounded retry program, or a separately proved
FS2 protocol/decoder instance. `multi` alone does not make the existing
`SamplerLawsD` a retry law. Mapping a finite retry chain's exhaustion to a
normal challenge still leaves a dyadic total law and does not cure exact
uniformity. Unbounded almost-sure termination is not supplied by the current
inductive finite `Sampler` either.

R417's theorem preserves `successMass n`; it is not a total-uniform law.
There are `C(262144,22) ≈ 2^326.0696` possible query sets, more than one block's
2^256 states. This reinforces the required multi-block/error treatment, but
no later A2 uniformity proof was attempted after the first false statement.

### D-SEM: no matching R0 semantic relation or per-prefix theorem

At R0_SOUNDNESS §7.2, the quoted 396430 numerator is V7's inventory. The tree
has stronger V7 ideal/measure theorems than that inventory alone, but their
relation, candidate timing, source objects and production hypotheses still
do not match R0. The three small opening terms (OOD mix 2, relation-alpha 24,
kappa-point-row 2) are part of its 30 independent roots; R0's opening proof
counts corresponding obligations separately. No numerical improvement was
inferred from that observation.

**Smallest change, not made:** specify R0's payment relation, source semantic
messages/challenges and ordering (including C1 before lambda/chi and C2 after),
its semantic verifier, the extraction-to-trace map, and its 87-claim layout
in R0_SOUNDNESS §2/§7. Then prove the matching R0 coverage/root bounds and a
per-prefix state invariant. The existing `Stmt.semantic : Prop` and
point-compatible `Witness` cannot express this theorem. The Lean interface
needs an outer protocol whose initial statement is public context and whose
prefix carries these messages and challenges; the opening theorem can remain
an unchanged subroutine. `SemStatement.SourceData` identifies these missing
definitions without assuming any of their correctness obligations.

An aggregate semantic error bound is not by itself FS2.D2's uniform bound at
**every** doomed prefix. The actual adaptive rounds must be represented and
their bad sets fixed before their challenges. Do not collapse all semantic
messages into a post-challenge statement or substitute a V7 premise.

### D-Z: two different circle experiments must not be conflated

For uniform draws from the full circle over K, the proved rows are
`2^31/(P^4-1)` and at most `(2^31+1)/(P^4-1)`, about **93 bits** each, not the
previous log's roughly 227-bit estimate. `BaseRational` contains 2^31 points,
not only the size-2^20 evaluation domain, and §2 chooses K, not WideExact.
This calculation is not a claim about the retained rejection sampler's error.

The retained source policy rejects the entire CM31 subfield; successful
points therefore have zero rational-event mass. Its distinct-second wrapper
also rejects equality. `CircleSource` proves those successful-outcome facts
from the actual retained definitions. R609/R945 keep both exhaustion errors
and give the successful point mass
`lambda * (1 + retry + retry^2)`, with
`lambda = ((1-(1/2^31)^8)/P)^4`, `retry = P^2*lambda`.
They do not say that a defaulted single block is uniform over Point K.

**Smallest change, not made:** R0_SOUNDNESS §2 must choose explicitly between
full-circle ideal draws with the above rows and the retained rejecting
circle/distinctness programs. In the latter case, specify verifier rejection
on exhaustion and represent both programs and intervening y0 absorption in
the outer state function. For a full-circle model, add both rows to §6 and
re-evaluate its claimed security parameters. The fixed five-round rb2 cannot
acquire these two rounds through a proof; its statement and round count would
have to be composed inside a new outer protocol. `SemStatement` only states
that extension's obligations. No D1/D2/D3 proof for it or end-to-end payment
knowledge-soundness theorem is claimed.

## Environment and verification

- Local inspection/editing: macOS worktree above. No local Lean dependency
  build or local full replay; no Rust gate, wallet or key operation.
- Build host: `dombarker@100.108.41.90`, hostname `nuc`, Linux
  `6.8.0-142-generic`, x86_64; physical RAM 66,698,665,984 bytes.
- Lean 4.32.0 Release, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Pinned workspace `T=/home/dombarker/project-offloads/aspis-fs-generic-20261006`.
  New real directories `T/sources/R0C` and `T/objects2/R0C` were used.
- Runner: `T/run2.sh <attempt> R0C/<Module> 7000 7`. It uses the previously
  captured `lake env` environment, then invokes that exact Lean binary with
  `-j1 -M7000 -DElab.async=false -R T/sources -o T/objects2/R0C/<Module>.olean`
  on the single changed source. No package-wide build was used to discover
  a local error. The runner, rather than a fresh Lake process, preserves the
  pinned object's import precedence documented in both prior logs.
- Every launch was its own `systemd-run --user --scope`, `MemoryHigh=5G`,
  `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, GNU `/usr/bin/time -v`,
  timeout 900 seconds. Exactly one Lean job at a time; no cap increase.
  Every reservation check reported populated 48 GiB + 7 GiB, admitted by the
  runner's 55 GiB working limit (leaving about 7.1 GiB physical RAM outside
  that reservation). No OOM, time limit or 24 GiB review point occurred.
- `LEAN_PATH`: `T/objects2` first, followed by captured Lake paths under
  `B=/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal`:
  `B/.lake/packages/{Cli,batteries,Qq,aesop,proofwidgets,importGraph,LeanSearchClient,plausible,mathlib}/.lake/build/lib/lean`
  in that order; then `B/.lake/build/lib/lean`; then
  `/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean`.
- Mirror roots: AspisFormal → `aspis-wide-replay-20261006/pinned-v7/AspisFormal`;
  Wide and WideTower.olean → `aspis-wide-replay-20261006/objects`;
  R0 → `T/R0-oleans-from-mac`; FS and FS2 → `T/objects/{FS,FS2}`;
  R0FS is the retained real directory; V8 and extracted roots →
  `aspis-r126-release-20260930-a/lib`. No dependency was rebuilt.
- The distinct-circle import additionally needed Aeneas and AeneasMeta.
  After attempts 512/513 reported missing roots, the mirror was extended to
  the **same pinned Aeneas library used by the r126 runner**:
  `/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean/{Aeneas,AeneasMeta,AeneasMeta.olean}`.
  These were environment repairs, not unchanged failing reruns or rebuilds.
- Final source revision: `1d4612dcd6ea21b8ee7bb7b5587b88cb58ae608c`;
  statement-only commit `7db5a56e7`; original interfaces remain at `810eabd4c`.
  Every final source SHA was checked against the local committed file and the
  host's `evidence/sha-<attempt>.txt`.
- After focused predecessor checks, exactly one final seven-file manifest
  replay ran, attempts 520–526, in the dependency order below. No frozen
  FS/FS2/R0/R0FS dependency or unrelated runtime/reproducibility suite reran.
  Final replay wall-time sum: 28.34 s. All exit 0, no warnings, zero swaps.
  Maximum final RSS 7,165,672 KiB ≈ 6.834 GiB, below the unchanged 7 GiB cap.
  Host-wide swap usage was nonzero from other work; these cgroups had no swap
  allocation and GNU time reported 0 swaps for every attempt.

### Final per-file evidence

PCQ means exactly `propext, Classical.choice, Quot.sound`. The statement file
contains definitions/Props only; no theorem is claimed or audited there.

| Attempt / target | SHA-256 | Exit | Wall | Peak RSS KiB | Swaps | Axioms |
|---|---|---:|---:|---:|---:|---|
| 520 / `lean/R0C/SemStatement.lean` | `a48c2b7e3a7b3de2260b4ac0e8861fcda31dccaf1a523a8bdd03d114fc5ca839` | 0 | 0:03.28 | 6794864 | 0 | definitions / Props only |
| 521 / `lean/R0C/Counting.lean` | `728ebfe472b0af967542358a717fb88fc69ac8e8becd4c1f763b83aeaccc31c1` | 0 | 0:01.76 | 3329644 | 0 | PCQ |
| 522 / `lean/R0C/Sampling.lean` | `bbcd664730a59e8429d2a9cbad00882e1680944e233db37cf9c2e549e09baaab` | 0 | 0:03.57 | 6783324 | 0 | PCQ |
| 523 / `lean/R0C/SamplerObstruction.lean` | `afd2d1809ead0f4480449385fb7ee1ae7fa1adbb718b3dfeca2182f3686a54a1` | 0 | 0:03.24 | 6787012 | 0 | PCQ; numeral divisibility: propext only |
| 524 / `lean/R0C/CircleRows.lean` | `a77a58a84660bdc9aa23e7084c9ae442e21059579697a881ce1b0a461e522f5c` | 0 | 0:03.62 | 6784712 | 0 | PCQ |
| 525 / `lean/R0C/CircleCard.lean` | `331ee06d13130c9932219d438e54aac1d92a4475353e4605cf14cb472181de55` | 0 | 0:03.75 | 6798376 | 0 | PCQ |
| 526 / `lean/R0C/CircleSource.lean` | `c65a90ff713914467bb8ce6778b95107ab7ced90b27ffa6d004f3606ba9959fc` | 0 | 0:09.12 | 7165672 | 0 | PCQ |

### Final #print axioms audit

```text
'R0C.Counting.mean_indicator_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.Counting.uniform_of_point_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.Counting.card_dvd_of_point_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.Counting.mean_or_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.Sampling.gamma_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.Sampling.defaultSet_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.Sampling.queries_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.SamplerObstruction.nonzero_card_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.SamplerObstruction.wide_nonzero_not_dvd_state' depends on axioms: [propext]
'R0C.SamplerObstruction.noSamplerLawsD' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleRows.baseRational_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleRows.z0_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleRows.z1_density_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleRows.chord_conditions' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleCard.split_circle_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleCard.qm31_circle_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleSource.model_success_not_rational' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleSource.distinct_success_conditions' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleSource.parameter_not_rational' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0C.CircleSource.source_success_not_rational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Failed attempts (one line each)

All are pre-final development attempts, not release evidence; no failing
object was consumed. Each retry changed source or repaired the identified
missing import environment. Raw stdout/time/source hashes remain in
`T/evidence/{out,time,sha}-<attempt>.*`. Compiler error recovery can print an
incomplete declaration audit on failures; all final audits above are clean.

| Attempt / target | Exit | Wall | RSS KiB | Swaps | Failure and replacement |
|---|---:|---:|---:|---:|---|
| 500 / `R0C/SemStatement.lean` | 1 | 0:03.06 | 6761296 | 0 | missing classical decision/Fintype instances; added local classical proposition decision |
| 502 / `R0C/Counting.lean` | 1 | 0:01.82 | 3313984 | 0 | union membership disjunction order; added or_comm |
| 504 / `R0C/SamplerObstruction.lean` | 1 | 0:03.11 | 6752848 | 0 | indicator_iff namespace and params1-hidden Fintype instance; opened FS and reduced params1 explicitly before abstract instantiation |
| 506 / `R0C/Sampling.lean` | 1 | 0:03.29 | 6750384 | 0 | Fin.val domain inference and let-bound query branch; annotated domain and reduced lets |
| 508 / `R0C/CircleRows.lean` | 1 | 0:03.23 | 6752060 | 0 | z0Bad-hidden subtype enumeration instance; unfolded predicate before generic count |
| 509 / `R0C/CircleRows.lean` | 1 | 0:03.49 | 6749200 | 0 | doc comment placed before omit command; moved omit before doc comment |
| 512 / `R0C/CircleSource.lean` | 1 | 0:00.98 | 2130168 | 0 | missing Aeneas root for distinct-circle source import; mirrored pinned r126 Aeneas library |
| 513 / `R0C/CircleSource.lean` | 1 | 0:01.38 | 2184868 | 0 | missing AeneasMeta root; mirrored pinned companion root and object |
| 515 / `R0C/CircleCard.lean` | 1 | 0:03.45 | 6764664 | 0 | R15/R0 QM31 instance selection and ambiguous P; selected R0 QM31 explicitly |
| 516 / `R0C/CircleCard.lean` | 1 | 0:03.83 | 6764648 | 0 | concrete subtype Fintype comparison blocked rw; tried equality composition |
| 517 / `R0C/CircleCard.lean` | 1 | 0:05.54 | 6767384 | 0 | concrete Point enumeration comparison reached recursion limit; replaced only the concrete cardinal interface with Nat.card, keeping the generic symbolic proof; no limit option added |

Preparation: initial scp failed because `sources/R0C` did not exist; created
the prescribed real source/object directories before attempt 500. No Lean ran.

Focused green predecessors: 501 (SemStatement, committed alone), 503
(Counting), 505 (SamplerObstruction), 507 (Sampling), 510 (CircleRows),
511 (first circle source-success facts), 514 (extended distinct-circle facts
after import repair), 518 (CircleCard). Attempt 519 was unused.

## Remaining premises of the fixed theorem

1. `SamplerLawsD`: **refuted**, not merely unproved, at WideExact and one
   32-byte state. No theorem with that hypothesis discharged was produced.
2. SEM/payment extraction: no matching R0 source theorem; remains outside
   the fixed opening theorem, whose extractor returns point-compatible tuples.
3. Step-3 conditions: ideal circle counts and retained successful-program
   facts are proved, but the fixed theorem still receives them in Stmt.
   Their sampler/error/transcript integration and the outer semantic state
   function are unproved. INJ remains discharged by the earlier FS2 proof.

Only the seven final Lean sources and this log are committed. No fixed
interface/specification, generated object, runner, evidence dump or existing
untracked repository file was changed or added to the commits.
