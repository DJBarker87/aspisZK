# Part 51: native simulator continuation

**Target not yet established.** Branch `codex/cx-prover-commit51-20261022`.
Only J10300–J10399 are authorized. No shipped crate or program file is changed.

## Endpoint before/after

Verbatim endpoint snapshots are in `evidence/prover-commit51-20261022/endpoint/`
under `docs/research/100bit-spend-path-20261013/`. They are identical to part 50.
`RustProverRefinement` remains explicit, with unchanged quantifiers and bound.

## Stage 1: duplicate declaration ownership

`Linear50` imports `Batched48` and reuses its byte-identical CM31/QM31
`mul_m31` definitions. No Session A module is edited. The replacement binder
checks the extraction bodies against that single retained owner so regeneration
preserves the fix. The six affected targets are rebuilt in J10300–J10305;
the combined audit is J10306. Shared sources and objects are snapshotted in the
branch-named host workspace before replacement. All needed dependents are
rebuilt with new dependency fingerprints.

Exact targets, source revisions/hashes, dependency fingerprints, exit status,
wall time, peak RSS, swap and full printed axioms are recorded in
`lean/attempts.json` and `lean/receipts/` in that evidence directory.
All jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
Lean retains the 7000 MiB internal limit. No cap increase is used.

## Stage 2: symbolic caller split

The old J10298 failed at `ProverCommitMaskArithmetic50.caller` with kernel
excessive memory consumption: exit 1, 19.10 s, 7170376 KiB, zero swaps.
The replacement first proves `ProverCommitBind51.three` over an arbitrary
carrier and arbitrary Result-valued callees. Concrete source conversion,
array construction, and all three callees are locally opaque at the composition
boundary. No large computation is reduced; the existing individual arithmetic
proofs are reused. `ProverCommitMaskArithmetic51.caller` keeps the exact old
coefficient-law premise, input quantifiers and conclusion. It passes J10311:
exit 0, 1.82 s, 4046236 KiB, zero swaps, standard axioms only.
J10307/08 are rejected symbolic let-normalization drafts; J10310 proves the
corrected helper. J10309 is retired before compilation (missing dependency
object). The coefficient producer remains the next obligation; this conditional
caller is not complete native selected-mask success.

## Stage 3a: complete selected-mask coefficient producer

J10317 proves the owned 26-write loop's canonical output and symbolic overwrite
sequence. J10316 proves the exact source destination schedule is injective,
bounded by 27, and omits 23. J10320 proves the generic overwrite invariant and
finite monomial coefficient laws; J10324 splits the combined schedule into the
16 c1 and 10 mask-only summands. No Boolean cube or large concrete term is
normalized. J10326 proves `ProverCommitMaskProducer51.exact_result`: actual
owned array production succeeds and every decoded output cell equals its
selected-mask polynomial coefficient. The old coefficient-image premise is
discharged in J10327 `ProverCommitMaskCaller51.exact_result`, composing producer,
linear forms, prepared Horner and final arithmetic. Canonical input values and
the explicit B.i/B.u basis representation equations remain; complete semantic
oracle provenance is still next. J10327: exit 0, 1.66 s, 4048744 KiB, zero
swaps, standard axioms only.

Native `coefficient-writes-v2` checks every output limb and paired tower-call
argument/order for arbitrary 26 inputs and arbitrary paired tower answers,
and checks the static schedule against the symbolic formula. Exit 0, 4.921 s,
586132 KiB, zero swaps. The first harness fails only on array-equality memcmp
unwinding; replacing the harness's equality with explicit limb comparisons
fixes it. Two initial extraction drafts omit the copied field module files;
those Rust compiler failures are retained. The corrected release-mode owner
extraction succeeds. Rejected Lean drafts and retired preflight J10319 are
retained; no source/cap is retried unchanged. Existing tower, linear, Horner
and finish native gates are reused with their unchanged source pins.

## Stage 3b: all mask-column reads and selected-mask value

J10330 proves all 26 complete sparse MLE calls and their destination reads
without an MLE-output premise. J10331 composes those reads, the G-column MLE,
and the complete selected-mask caller. `claims_value` identifies each read
with `honestClaims t a 0`; canonical input arrays and their usual trace
representation are the inputs, not an output equality. The native full-context
column-loop gate checks all 26 outputs, all point operands and ordered column
handles, exit 0, 27.266 s, 1166888 KiB, zero swaps. Column handles stand for
read-only arrays; each complete array MLE's value is the separate Lean proof.
J10329's opaque-value conversion reaches default recursion depth; explicitly
unfolding only the named symbolic value at that proof step fixes it in J10330.
No recursion-depth or heartbeat setting is raised. J10331: exit 0, 1.78 s,
4086212 KiB, zero swaps, standard axioms. This is the semantic oracle's mask
component, not yet its extra-plus-terminal value or success theorem.

## Stage 3c: native basis and exact extra functional

J10338 constructs a concrete M31 subfield basis in QM31, and J10340
instantiates the complete mask-read theorem with it: no B.i/B.u representation
premises remain in `ProverCommitConcreteMask51.exact_result`. J10333/37 identify
the complete two reverse-Horner extra evaluations with the model Libra dot
product. J10341 gives `honestExtra` from explicit coefficient inputs (their
permutation provenance is addressed next). J10342 proves both native inverse
branches, including Some-success implying nonzero input; this is a local
arithmetic fact, not a full P_R1-source domain theorem.

J10343 proves symbolic hom transport of the entire mask formula. J10345 maps
the native basis to the retained `PrivacyR1AcctBasis.basis` in WideExact, and
J10349 transports all three statement points, all honest claims, and the
Libra/extra functional between fields. The first concrete extra-sum rewrite
fails at concrete instance inference; a generic Field lemma fixes it without
normalizing the carrier. Rejected conditional-simplifier drafts and missing
cache preflight J10344 are retained. The replacement reuses the cached account
basis rather than building an unrelated cold Session A dependency closure.
All accepted axioms remain standard. None of these transport results is
promoted to the full terminal/oracle result.

## Stage 3d: coefficient provenance and complete linear oracle component

J10348/50 prove the complete independent owned 1024-cell coefficient producer
and its exact `coeffsOf AspisR1.rowEquiv` image. J10351 composes it with the extra
evaluator, discharging the coefficient input law of J10341. J10352/55 compose
the native mask and extra values on WideExact:
`ProverCommitLinearOracle51.exact_result` concludes exactly
`embed (decode z) = R0Z.PayloadSplit.maskLinear AspisR1.rowEquiv
ProverCommitWideBasis51.basis a mappedTrace`. It needs only canonical point/
column inputs and the ordinary input trace representation; no mask, MLE,
coefficient or extra output/model identity is a premise. J10355: exit 0,
2.41 s, 4207016 KiB, zero swaps, standard axioms.

The full native `Variant::coefficients` `from_fn` gate times out at 180.002 s,
exit 124, cgroup peak 3372949504 bytes, zero swaps. Its GNU-time RSS is only
15652 KiB because it measures the timeout parent; the aggregate cgroup peak
is retained explicitly. It is not accepted and is not rerun unchanged. The
loop trace isolates standard-library array construction and Kani's arbitrary
array creation. The narrowed row callback initially still enters array creation
and hits the harness unwind guard; removing that irrelevant array construction
leaves the arbitrary-index row kernel, which passes in 0.292 s / 128776 KiB.
The full owned Lean array result and native row kernel are established; a
complete native `from_fn` constructor refinement is not claimed from that
narrower gate. No new TrustedStd field is introduced.

J10354 proves the exact source half-inverse prefix's None iff alpha9=half,
Some-success implies alpha9!=half, and its canonical inverse value. The native
accepted-prefix control-flow gate (public-data/emit/convert/build/check and
panic rejection, with universal suffix outcomes) passes in 0.307 s / 137080
KiB, zero swaps. This does not by itself instantiate the complete P_R1 checker
or discharge its other source/domain obligations.

## Stage 3e: terminal equality product and full arithmetic suffix

J10360 proves the complete owned ten-factor equality loop. J10364 proves its
generic head split; J10365 proves the complete `eqValue` result. The concrete
head conversion in J10363 reaches default heartbeats; it is replaced by the
generic symbolic lemma, not a larger budget or cap. J10366/67 prove all eight
suffix field calls and their composition with `eqValue`, including the zero-H1
specialization. Only canonical component inputs remain; the source composition
producer is still upstream, not presumed proved. All printed axioms are standard.
The equality-loop native paired-callee trace gate passes: exit 0, 9.136 s,
610864 KiB, zero swaps. The suffix gate passes: exit 0, 6.649 s, 415292 KiB,
zero swaps. Native source spans and their hashes are retained separately.

## Demonstrated terminal integration obstruction

The retained `CompositionPartsAfterValidationExact.run_success_of_poseidon_contract`
is conditional on a callable Poseidon success/value contract. Its candidate
packed-family route also retains explicit leading/full source-call, canonicality
and model premises. These must be instantiated with the frozen native functions;
they are not supplied by the new equality/suffix arithmetic.

Read-only `pins/terminal-cone-preflight.json` follows the three relevant retained
cones using four explicit canonical source roots. It resolves 535 project
modules, of which **495 have no object in Env J** (40 are cached); 54 imports
outside those roots are left unresolved rather than guessed. This is a lower
bound on the missing build closure, not a coherent replay. At J10367 only
J10368–J10399 (32 numbers) remain, and one module per attempt is mandatory.
Replaying even the resolved missing closure exceeds this allocation. No Session A
module or object is replaced, no cold dependency campaign is launched, and no
conditional terminal contract is treated as an implementation theorem. This is
the demonstrated obstruction to continuing the retained integration route here;
it is not a counterexample to the desired native payload equality.

The accepted deliverable reaches the complete owned linear oracle value and
the terminal arithmetic component. It does **not** establish full native semantic
oracle success, its terminal producer, the running-claim/boundary/terminal guard
composition, interpolation/original-round assembly, or complete source P_R1
good-domain transfer. Interfaces 4–6 are not advanced as complete interfaces;
the coefficient permutation above is a prerequisite for interface 3's extra.
Full Weights::new/gamma batching, source opening helper binding and complete
native simulator payload equality remain open. `RustProverRefinement` stays
explicit; no FSExperiments conversion or joins were attempted.

## Verbatim deployed endpoint before/after

Before:

```lean
import R1Z.PrivacyR1HeadlineDeployed
import R1Z.ProverCommitFuelJoin22
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitDeployedFuel22
abbrev ownedDecode := ProverCommitOwnedDecoder.decoder (K := PrivacyR1AcctBasis.K)
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
open R1Z.PrivacyR1Headline
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
local notation "L₁" => PrivacyR1AcctModel.L₁
local notation "L₂" => PrivacyR1AcctModel.L₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux)

local notation "log" => PhaseWireLog2Bin.log
local notation "base" => PrivacyR1AcctModel.base template log
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

def input : HonestProver K := BuilderSource.prover

variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
local notation "decode" => ownedDecode

local notation "fib" => PhaseWireLog2Bin.fib
local notation "opens" => PhaseWireLog2Bin.opens
local notation "seed" => PrivacyR1AcctModel.seed
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) decode fib opens
open R1Z.PrivacyR1HeadlineWire2
local notation "raw" => fsR1P
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))
  (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))
  8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
local notation "coins" => PrivacyR1AcctModel.wire_coins template log h outputs x
local notation "W" => R1Z.PhaseLocalityBin.R1PhaseWire.toWire
  (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)
local notation "Pr" => R1Z.PhaseLocalityBin.R1PhaseProver.toProver
  (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)

local notation "source" => ProverCommitReencode16.experiment W Pr 8 eight_pos
  (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
  ProverCommitReencode16.encode

/-- Equality of the full observable execution and the observer's decision,
not merely equality of acceptance or a hash. The independently supplied
runtime must include builder/checker/retry, ordered wire and oracle history
in its FS experiment. No concrete Rust instance is supplied here. -/
structure WholeRunJoin {R M : Type} [Fintype R] [Fintype M]
    (runtime : R → ROMView K CommitHandle Aux R1Bat × Bool)
    (model : M → ROMView K CommitHandle Aux R1Bat × Bool)
    (bad : Fin 8 → M → Prop) where
  cp : Coupling R M
  agreement : ∀ s, ¬ (∃ i, bad i (cp.toM s)) →
    runtime (cp.toR s) = model (cp.toM s)

def WholeRunJoin.tests {R M : Type} [Fintype R] [Fintype M]
    {runtime : R → ROMView K CommitHandle Aux R1Bat × Bool}
    {model : M → ROMView K CommitHandle Aux R1Bat × Bool}
    {bad : Fin 8 → M → Prop} (join : WholeRunJoin runtime model bad) :
    ModelExecutionJoin (fun r => bit (runtime r).2) (fun m => bit (model m).2) bad where
  cp := join.cp
  agreement := fun s hn => congrArg (fun run => bit run.2) (join.agreement s hn)

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
  [Fintype rust.RealRand] [Nonempty rust.RealRand]
  [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
  (observer_program : rust.Adversary → View K CommitHandle Aux R1Bat →
    List (List UInt8 × OracleAnswer) → OProg)

/-- The explicit deployed obligation. Both sides include the complete public
view, ordered observer history and observer decision. The exceptions are the
existing realBad/selectedBad, not predicates chosen by the implementation. -/
def LegacyRustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (WholeRunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w))) ∧
  (∀ adv : rust.Adversary, Nonempty (WholeRunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad))

/-- Exact adversary-only query suffix of the underlying ordered source. -/
def realSeedQueries (adv : rust.Adversary) (w : (h).Instance) : (source).RealRand →
    List ProverCommitSeedEvent19.Entry :=
  ProverCommitObserverQueries19.real W Pr 8
    (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs
    (ProverCommitReencode16.observer ProverCommitReencode16.encode
      (RomObserverBin.observerMap rust observer_program adv)) x w

def idealSeedQueries (adv : rust.Adversary) : (source).IdealRand →
    List ProverCommitSeedEvent19.Entry :=
  ProverCommitObserverQueries19.ideal W 8 eight_pos
    (P_R1 (h).transport B hB) (simE (h).transport B outputs x)
    (ProverCommitReencode16.observer ProverCommitReencode16.encode
      (RomObserverBin.observerMap rust observer_program adv)) x

/-- The explicit deployed obligation. Both sides include the complete public
view, ordered observer history and observer decision. The exceptions are the
fixed parser events augmented with seed-guess and five-draw exhaustion events on an
independently retained model seed. Query functions are fixed by the model. -/
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

/-- Every previous certificate still suffices. The independent seed is added
by product extension, so this is an actual implication between premises. -/
theorem legacy_refinement_implies
    (old : LegacyRustProverRefinement template outputs x rust observer_program) :
    RustProverRefinement template outputs x rust observer_program := by
  constructor
  · intro adv w hw
    let join := Classical.choice (old.1 adv w hw)
    exact ⟨ProverCommitFuelJoin22.of_seed (ProverCommitSeedJoin19.of_old _ _ _ _ join.cp join.agreement)⟩
  · intro adv
    let join := Classical.choice (old.2 adv)
    exact ⟨ProverCommitFuelJoin22.of_seed (ProverCommitSeedJoin19.of_old _ _ _ _ join.cp join.agreement)⟩


/-- Deletion-free implication: every previously valid deployed refinement
also satisfies the enlarged fixed event. No concrete source join is asserted. -/
theorem seed_refinement_implies
    (old : PrivacyR1HeadlineDeployed.RustProverRefinement template outputs x rust observer_program) :
    RustProverRefinement template outputs x rust observer_program := by
  constructor
  · intro adv w hw
    exact ⟨ProverCommitFuelJoin22.of_seed (Classical.choice (old.1 adv w hw))⟩
  · intro adv
    exact ⟨ProverCommitFuelJoin22.of_seed (Classical.choice (old.2 adv))⟩

#print axioms seed_refinement_implies


attribute [local irreducible] PrivacyR1AcctBasis.basis
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100 := by
  have model := PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver.privacy_headline_admitted
    template outputs x
  have caller := ProverCommitOwnedEndpoint.caller_law template input outputs x
  obtain ⟨hc₁,hc₂,hs₁,hs₂,hcount,hb₁,hb₂⟩ := ProverCommitCallerInstance.budgets Pr caller
  have hM := ProverCommitModelCore16.read_bound W Pr L₁ L₂ hcount hb₁ hb₂
  have hk := QueryScanFreshNumerics.lazy_budget_le_fresh hM
    (Nat.succ_le_succ (Nat.zero_le (8 * n1 W Pr)))
  constructor
  · intro adv w hw
    have hr₀ := ProverCommitFuelJoin22.test_bound
      (Classical.choice (refinement.1 adv w hw)) (fun run => bit run.2)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
      (fun r => ProverCommitObserverQueries19.real_bound W Pr 8
        (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs _ x w r)
    have hi₀ := ProverCommitFuelJoin22.test_bound
      (Classical.choice (refinement.2 adv)) (fun run => bit run.2)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
      (fun r => ProverCommitObserverQueries19.ideal_bound W 8 eight_pos
        (P_R1 (h).transport B hB) (simE (h).transport B outputs x) _ x r)
    have hscan : 8 * scanProbability ≤ 8 / (2 : ℚ)^486 := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left scan_probability_le (by norm_num : (0 : ℚ) ≤ 8)
    have hr := hr₀.trans (add_le_add (add_le_add
      ((ProverCommitModelCore16.real_bad_mass base h B outputs x seed hc₁ hc₂ w).trans
        (add_le_add (le_refl _) hscan)) (le_refl (ProverCommitSeedEvent19.budget (2^64)))) (le_refl ProverCommitFuelMass22.charge))
    have idealMass : eventMass (fun r : (source).IdealRand => ∃ i : Fin 8, QueryScanIdealHistory.selectedBad i r) ≤
        8 * scanProbability := by
      exact R0Z.FsAbortBounds.mass_exists_le_card _ _
        (fun i => QueryScanIdealHistory.selected_bad_mass i)
    have hi := hi₀.trans (add_le_add (add_le_add (idealMass.trans hscan)
      (le_refl (ProverCommitSeedEvent19.budget (2^64)))) (le_refl ProverCommitFuelMass22.charge))
    obtain ⟨hpub, hs⟩ := PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises (x := x) w hw
    have core := ProverCommitModelCore16.core_privacy base h B outputs x seed hB hpub hs
      ProverCommitSourceDecoder.quotientFibreSize (by
        intro τ
        convert ProverCommitCallerInstance.fibres Pr caller τ using 2
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      L₁ L₂ (ProverCommitCallerInstance.exhaustion Pr caller)
      hc₁ hc₂ hs₁ hs₂ coins
      (PhaseWireLog2Bin.batches input outputs x template decode)
      (PhaseWireLog2Bin.ordered_log input outputs x template decode) hcount hb₁ hb₂
    have mid := ProverCommitReencode16.privacy_transport _ _ _ _ _ _
      ProverCommitReencode16.encode _ _ _ _ _ core
    have hmid := mid (RomObserverBin.observerMap rust observer_program adv) w hw
    have t₁ := abs_sub_le
      (mean (realTest h B outputs rust adv x w))
      (mean (realTest h B outputs source (RomObserverBin.observerMap rust observer_program adv) x w))
      (mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
        (simE (h).transport B outputs x)))
    have t₂ := abs_sub_le
      (mean (realTest h B outputs rust adv x w))
      (mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
        (simE (h).transport B outputs x)))
      (mean (idealTestS rust adv x (simE (h).transport B outputs x)))
    rw [abs_sub_comm] at hi
    calc _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
          ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) + modelError W Pr L₁ L₂) +
          (8 / (2 : ℚ)^486 + ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) :=
            t₂.trans (add_le_add (t₁.trans (add_le_add hr hmid)) hi)
         _ = modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 +
           QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) +
           2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge := by ring
         _ ≤ _ := add_le_add (add_le_add (add_le_add (le_refl _) hk) (le_refl _)) (le_refl _)
  · constructor
    · exact add_le_add (add_le_add model.2.1 (le_refl _)) (le_refl _)
    · apply (add_le_add (add_le_add model.2.1 (le_refl _)) (le_refl _)).trans_lt
      exact ProverCommitFuelMass22.total_lt_target
        (Nat.le_trans (Nat.add_le_add_right hM 1) (by norm_num)) (Nat.le_refl _)

#print axioms WholeRunJoin.tests
#print axioms legacy_refinement_implies
#print axioms privacy_headline_deployed
end R1Z.ProverCommitDeployedFuel22

```

After:

```lean
import R1Z.PrivacyR1HeadlineDeployed
import R1Z.ProverCommitFuelJoin22
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitDeployedFuel22
abbrev ownedDecode := ProverCommitOwnedDecoder.decoder (K := PrivacyR1AcctBasis.K)
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
open R1Z.PrivacyR1Headline
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
local notation "L₁" => PrivacyR1AcctModel.L₁
local notation "L₂" => PrivacyR1AcctModel.L₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux)

local notation "log" => PhaseWireLog2Bin.log
local notation "base" => PrivacyR1AcctModel.base template log
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

def input : HonestProver K := BuilderSource.prover

variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
local notation "decode" => ownedDecode

local notation "fib" => PhaseWireLog2Bin.fib
local notation "opens" => PhaseWireLog2Bin.opens
local notation "seed" => PrivacyR1AcctModel.seed
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) decode fib opens
open R1Z.PrivacyR1HeadlineWire2
local notation "raw" => fsR1P
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))
  (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))
  8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
local notation "coins" => PrivacyR1AcctModel.wire_coins template log h outputs x
local notation "W" => R1Z.PhaseLocalityBin.R1PhaseWire.toWire
  (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)
local notation "Pr" => R1Z.PhaseLocalityBin.R1PhaseProver.toProver
  (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)

local notation "source" => ProverCommitReencode16.experiment W Pr 8 eight_pos
  (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
  ProverCommitReencode16.encode

/-- Equality of the full observable execution and the observer's decision,
not merely equality of acceptance or a hash. The independently supplied
runtime must include builder/checker/retry, ordered wire and oracle history
in its FS experiment. No concrete Rust instance is supplied here. -/
structure WholeRunJoin {R M : Type} [Fintype R] [Fintype M]
    (runtime : R → ROMView K CommitHandle Aux R1Bat × Bool)
    (model : M → ROMView K CommitHandle Aux R1Bat × Bool)
    (bad : Fin 8 → M → Prop) where
  cp : Coupling R M
  agreement : ∀ s, ¬ (∃ i, bad i (cp.toM s)) →
    runtime (cp.toR s) = model (cp.toM s)

def WholeRunJoin.tests {R M : Type} [Fintype R] [Fintype M]
    {runtime : R → ROMView K CommitHandle Aux R1Bat × Bool}
    {model : M → ROMView K CommitHandle Aux R1Bat × Bool}
    {bad : Fin 8 → M → Prop} (join : WholeRunJoin runtime model bad) :
    ModelExecutionJoin (fun r => bit (runtime r).2) (fun m => bit (model m).2) bad where
  cp := join.cp
  agreement := fun s hn => congrArg (fun run => bit run.2) (join.agreement s hn)

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
  [Fintype rust.RealRand] [Nonempty rust.RealRand]
  [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
  (observer_program : rust.Adversary → View K CommitHandle Aux R1Bat →
    List (List UInt8 × OracleAnswer) → OProg)

/-- The explicit deployed obligation. Both sides include the complete public
view, ordered observer history and observer decision. The exceptions are the
existing realBad/selectedBad, not predicates chosen by the implementation. -/
def LegacyRustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (WholeRunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w))) ∧
  (∀ adv : rust.Adversary, Nonempty (WholeRunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad))

/-- Exact adversary-only query suffix of the underlying ordered source. -/
def realSeedQueries (adv : rust.Adversary) (w : (h).Instance) : (source).RealRand →
    List ProverCommitSeedEvent19.Entry :=
  ProverCommitObserverQueries19.real W Pr 8
    (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs
    (ProverCommitReencode16.observer ProverCommitReencode16.encode
      (RomObserverBin.observerMap rust observer_program adv)) x w

def idealSeedQueries (adv : rust.Adversary) : (source).IdealRand →
    List ProverCommitSeedEvent19.Entry :=
  ProverCommitObserverQueries19.ideal W 8 eight_pos
    (P_R1 (h).transport B hB) (simE (h).transport B outputs x)
    (ProverCommitReencode16.observer ProverCommitReencode16.encode
      (RomObserverBin.observerMap rust observer_program adv)) x

/-- The explicit deployed obligation. Both sides include the complete public
view, ordered observer history and observer decision. The exceptions are the
fixed parser events augmented with seed-guess and five-draw exhaustion events on an
independently retained model seed. Query functions are fixed by the model. -/
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

/-- Every previous certificate still suffices. The independent seed is added
by product extension, so this is an actual implication between premises. -/
theorem legacy_refinement_implies
    (old : LegacyRustProverRefinement template outputs x rust observer_program) :
    RustProverRefinement template outputs x rust observer_program := by
  constructor
  · intro adv w hw
    let join := Classical.choice (old.1 adv w hw)
    exact ⟨ProverCommitFuelJoin22.of_seed (ProverCommitSeedJoin19.of_old _ _ _ _ join.cp join.agreement)⟩
  · intro adv
    let join := Classical.choice (old.2 adv)
    exact ⟨ProverCommitFuelJoin22.of_seed (ProverCommitSeedJoin19.of_old _ _ _ _ join.cp join.agreement)⟩


/-- Deletion-free implication: every previously valid deployed refinement
also satisfies the enlarged fixed event. No concrete source join is asserted. -/
theorem seed_refinement_implies
    (old : PrivacyR1HeadlineDeployed.RustProverRefinement template outputs x rust observer_program) :
    RustProverRefinement template outputs x rust observer_program := by
  constructor
  · intro adv w hw
    exact ⟨ProverCommitFuelJoin22.of_seed (Classical.choice (old.1 adv w hw))⟩
  · intro adv
    exact ⟨ProverCommitFuelJoin22.of_seed (Classical.choice (old.2 adv))⟩

#print axioms seed_refinement_implies


attribute [local irreducible] PrivacyR1AcctBasis.basis
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100 := by
  have model := PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver.privacy_headline_admitted
    template outputs x
  have caller := ProverCommitOwnedEndpoint.caller_law template input outputs x
  obtain ⟨hc₁,hc₂,hs₁,hs₂,hcount,hb₁,hb₂⟩ := ProverCommitCallerInstance.budgets Pr caller
  have hM := ProverCommitModelCore16.read_bound W Pr L₁ L₂ hcount hb₁ hb₂
  have hk := QueryScanFreshNumerics.lazy_budget_le_fresh hM
    (Nat.succ_le_succ (Nat.zero_le (8 * n1 W Pr)))
  constructor
  · intro adv w hw
    have hr₀ := ProverCommitFuelJoin22.test_bound
      (Classical.choice (refinement.1 adv w hw)) (fun run => bit run.2)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
      (fun r => ProverCommitObserverQueries19.real_bound W Pr 8
        (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs _ x w r)
    have hi₀ := ProverCommitFuelJoin22.test_bound
      (Classical.choice (refinement.2 adv)) (fun run => bit run.2)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
      (fun r => ProverCommitObserverQueries19.ideal_bound W 8 eight_pos
        (P_R1 (h).transport B hB) (simE (h).transport B outputs x) _ x r)
    have hscan : 8 * scanProbability ≤ 8 / (2 : ℚ)^486 := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left scan_probability_le (by norm_num : (0 : ℚ) ≤ 8)
    have hr := hr₀.trans (add_le_add (add_le_add
      ((ProverCommitModelCore16.real_bad_mass base h B outputs x seed hc₁ hc₂ w).trans
        (add_le_add (le_refl _) hscan)) (le_refl (ProverCommitSeedEvent19.budget (2^64)))) (le_refl ProverCommitFuelMass22.charge))
    have idealMass : eventMass (fun r : (source).IdealRand => ∃ i : Fin 8, QueryScanIdealHistory.selectedBad i r) ≤
        8 * scanProbability := by
      exact R0Z.FsAbortBounds.mass_exists_le_card _ _
        (fun i => QueryScanIdealHistory.selected_bad_mass i)
    have hi := hi₀.trans (add_le_add (add_le_add (idealMass.trans hscan)
      (le_refl (ProverCommitSeedEvent19.budget (2^64)))) (le_refl ProverCommitFuelMass22.charge))
    obtain ⟨hpub, hs⟩ := PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises (x := x) w hw
    have core := ProverCommitModelCore16.core_privacy base h B outputs x seed hB hpub hs
      ProverCommitSourceDecoder.quotientFibreSize (by
        intro τ
        convert ProverCommitCallerInstance.fibres Pr caller τ using 2
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      L₁ L₂ (ProverCommitCallerInstance.exhaustion Pr caller)
      hc₁ hc₂ hs₁ hs₂ coins
      (PhaseWireLog2Bin.batches input outputs x template decode)
      (PhaseWireLog2Bin.ordered_log input outputs x template decode) hcount hb₁ hb₂
    have mid := ProverCommitReencode16.privacy_transport _ _ _ _ _ _
      ProverCommitReencode16.encode _ _ _ _ _ core
    have hmid := mid (RomObserverBin.observerMap rust observer_program adv) w hw
    have t₁ := abs_sub_le
      (mean (realTest h B outputs rust adv x w))
      (mean (realTest h B outputs source (RomObserverBin.observerMap rust observer_program adv) x w))
      (mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
        (simE (h).transport B outputs x)))
    have t₂ := abs_sub_le
      (mean (realTest h B outputs rust adv x w))
      (mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
        (simE (h).transport B outputs x)))
      (mean (idealTestS rust adv x (simE (h).transport B outputs x)))
    rw [abs_sub_comm] at hi
    calc _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
          ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) + modelError W Pr L₁ L₂) +
          (8 / (2 : ℚ)^486 + ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) :=
            t₂.trans (add_le_add (t₁.trans (add_le_add hr hmid)) hi)
         _ = modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 +
           QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) +
           2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge := by ring
         _ ≤ _ := add_le_add (add_le_add (add_le_add (le_refl _) hk) (le_refl _)) (le_refl _)
  · constructor
    · exact add_le_add (add_le_add model.2.1 (le_refl _)) (le_refl _)
    · apply (add_le_add (add_le_add model.2.1 (le_refl _)) (le_refl _)).trans_lt
      exact ProverCommitFuelMass22.total_lt_target
        (Nat.le_trans (Nat.add_le_add_right hM 1) (by norm_num)) (Nat.le_refl _)

#print axioms WholeRunJoin.tests
#print axioms legacy_refinement_implies
#print axioms privacy_headline_deployed
end R1Z.ProverCommitDeployedFuel22

```

