# Part 52: terminal dependency closure and simulator continuation

**Target not yet established.** Branch `codex/cx-prover-commit52-20261022`.
Only J10400–J10499 are authorized for proof attempts. Cold dependency work uses
separate BUILD-52 labels. No shipped crate or program source is changed.

## Stage 1: cold dependency preflight

BUILD-52-1 ran the pinned terminal-cone preflight in a dedicated host scope:
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. The populated host
reservation before launch was 26172456960 bytes plus this scope's 8 GiB.
The scope exited before any Lean invocation: Env J lacks both objects and
staged sources for eleven external imports. The first unresolved module is
`AspisR1SelectedMaskProbe.Funs`. Exact console and GNU-time output are retained
under `evidence/prover-commit52-20261022/build/` in the 100bit-spend-path tree.
Exit 1; wall 0.07 s; peak RSS 31184 KiB; swaps 0; source revision
`223a37671e784ddeeab6bd8295df24fdb2647a79`; axioms audit not applicable (no Lean
compile and no new theorem).

Read-only source resolution expanded the preflight to retained extraction
evidence and the retained Lean 4.32 arithmetic port. The resolver accepts
additional repository copies only when all candidate bodies have the same
SHA-256; its decisions are in `build/resolution.json`. The two missing
SelectedMask field modules use the audited arithmetic port's unchanged
`sources/` files, with original paths and hashes in `build/plan.json`.

The expanded preflight succeeds and schedules **529 missing modules**. The
single compiler pass is BUILD-52-2 (BUILD-52-1 invoked no compiler). It runs
sequentially in one scope with the same limits, asserts the actual cgroup
settings, monitors aggregate child RSS, stops near 7.5 GiB RSS or after ten
minutes without a new target, and stops at the first compiler failure. Existing
objects are reused and never overwritten. No Session A source is edited.
The J10400–J10499 launcher preserves the existing no-unchanged-rerun guard.

## Cold compiler result and isolated obstruction

**BUILD-52-2 failed at module 262 after 261 successful module builds.**
Exact targets are the three roots in `build/plan.json`. Source revision:
`223a37671e784ddeeab6bd8295df24fdb2647a79`. Exit 1; total GNU-time wall
490.65 s (driver module-pass wall 490.5145 s); peak GNU-time RSS 4170212 KiB;
maximum sampled aggregate RSS 4294701056 bytes; swaps 0. The cgroup memory
peak is 675958784 bytes, a distinct charged-memory metric rather than RSS.
All memory high/max/OOM/kill event counts are zero. The scope is inactive.

`build/modules-audited.json` records every attempted module's source SHA,
dependency fingerprint, exact compiler command, exit, wall, GNU-time peak RSS,
sampled aggregate RSS, swaps, source revision and complete printed axiom reports.
All **552 printed axiom reports** in the cold pass use only subsets of
`[propext, Classical.choice, Quot.sound]`; full outputs are also preserved in
the per-module logs. Modules without a printed report are not described as
freshly audited declarations. No new theorem is introduced by the cold build.
`build/built-objects.json` records SHA-256 and size for the 261 new shared-cache
objects; no binary is committed. No prior shared object is overwritten.

The failing module is `ExtractedDecoderCallerBridge`, source SHA
`d7b5678e7626bcdfa93b630018b594332a484cbb92dc54151519bd9ca141c29d`,
label `BUILD-52-2-262`: exit 1, wall 0.7525 s, peak RSS 1855512 KiB,
zero swaps. Its verbatim error is:

```text
error: import AspisR1TerminalDecoder.Types failed, environment already contains 'instDiscriminantPoolV1TransitionKindU8' from AspisR1WithdrawalCaller.Types
```

Both owners compiled individually in this same pass: caller Types at 254 and
decoder Types at 257. The generated `@[discriminant u8 [1,2]]` attributes on
their distinct namespaced `pool_v1.historical_anchor.PoolV1TransitionKind`
types create the same unqualified instance name. This is an import-union
collision, not pathological reduction or a memory failure. The exact source
spans, hashes, complete compiler error and dependency path to
`CompositionPartsAfterValidationExact` are in `build/obstruction.json`.

The pass stops at this failure. There is no compiler rerun, no cap increase,
and no Session A edit. The task explicitly permits building Session A's
modules but prohibits editing them. The concrete next owner repair is to give
the generated discriminant instances type-qualified names while preserving
their readers and constructor tags, then rebuild the affected import union
and dependents. This repair has not been performed here.

The read-only post-failure inventory (`build/remaining-closure.json`) finds
121 missing objects in the composition root, including the failed bridge;
144 in the separate Poseidon candidate root; and three in the independent
arithmetic root. Finishing the Poseidon cone one module per proof attempt
exceeds the entire 100-number allocation. No second cold compiler pass or
broader manifest replay is launched.

## Independent arithmetic continuation

The independent retained equality-product/loop and terminal arithmetic suffix
pass separately under J10400–J10402. They do not import the colliding
decoder/caller union. These are unchanged retained proofs, not discharge of
their upstream composition input. Exact receipts follow in `build/J104*.json`.
All three use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
Lean `-M7000`, and the same source revision recorded above. Every printed
axiom report is exactly `[propext, Classical.choice, Quot.sound]`.

| Attempt | Exact module | Exit | Wall (s) | Peak RSS (KiB) | Swaps |
|---|---|---:|---:|---:|---:|
| J10400 | EqualityValueProduct | 0 | 1.58 | 3964372 | 0 |
| J10401 | EqualityValueLoop | 0 | 2.18 | 3989976 | 0 |
| J10402 | TerminalPartsArithmeticExact | 0 | 1.70 | 3972380 | 0 |

J10403–J10499 remain unused. No complete manifest is replayed after the cold
failure; unchanged adversarial/runtime/ELF suites are not rerun. No file under
`crates/` or `programs/` changes, so the shipped-file rebuild rule is not
triggered. No ELF byte-identity rerun is claimed. No wallet or key is touched.

The helper initially tried executing the non-executable launcher directly;
the OS rejected it before any compiler invocation. Invoking the existing
launcher with `sh` fixes that tooling issue; no Lean input is retried.

## Contract inspection and remaining interfaces

Read-only inspection identifies `PoseidonLeadingPairExact.source_success`
and `PoseidonInterpolatedFullPairExact.qm_source_success` as potential inputs
to the candidate callable contract. Their additional import closure is not
compiled. Two missing original Session A source files are retained byte-for-byte
under `retained-sources/`, with origin paths and SHA-256 pins; they are evidence
recovery only and are not new accepted theorem results.

The retained projected wrapper pins extraction-candidate Rust SHA
`82d54bbade8d81899c64ede23befce8b240b881d61b144e769c0d0e16ab5cff9`;
the current frozen `crates/aspis-statement/src/state_only_poseidon.rs` has SHA
`4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe`.
Those whole-file hashes alone neither establish nor refute the required
function-level correspondence. No candidate theorem is promoted to a native
source contract without that binding.

No source Poseidon contract, complete interface 3 integration, or interface
4–6 closure is claimed. Remaining: complete semantic oracle/terminal producer,
guards and original-round assembly; complete Weights/gamma batching; source
opening helper/caller composition; and native simulator output equal to the
`R0Z.RefPayload.simE` payload. The deployed `RustProverRefinement` premise,
quantifiers, failure events and bound remain unchanged. No FSExperiments
conversion or joins are attempted. **Target not yet established.**

## Endpoint before/after

Both complete verbatim endpoints follow below and are also preserved in
`endpoint/before.lean.txt` and `endpoint/after.lean.txt`. They are byte-identical
to the unchanged repository source; SHA-256 and size are in `endpoint/pins.json`.
The existing endpoint's part 51 audit is reused; no unchanged replay is run.
The deployed refinement remains explicit; no premise or bound is weakened.

## Verbatim endpoint before

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

## Verbatim endpoint after

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
