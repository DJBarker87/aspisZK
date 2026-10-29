import R1Z.ProverCommitDeployedFuel22
import PV_EVHD_Interface
/-! EXPERIMENTAL, NOT ADOPTED (D478). A conditional event-retaining headline.
No deployed Runtime, simulator, observer, bound or trust field is edited. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVHD_Headline
open R1Z
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


open PV_RJ4IDB PV_EVHD_Interface
variable {Public Signal Env A R : Type} [Fintype R] [Nonempty R]

/-- EXPERIMENTAL: both adaptive queries and the final decision see the full
ordered trace and public failure signal; no successful-return restriction. -/
structure Observer (Signal A : Type) where
  program : Signal × Observation A → OProg
  decide : Signal × Observation A → Bool

variable (completion : Completion Public Signal Env (ROMView K CommitHandle Aux R1Bat) A)
    (pubData : Public) (env : Env)

def completed (v : ROMView K CommitHandle Aux R1Bat) : Signal × Observation A :=
  observe (completion.signal pubData env)
    (completion.complete pubData (completion.signal pubData env) env v)

/-- EXPERIMENTAL: arbitrary event observers are pulled back to existing
adaptive model observers. Source causality/reachability is a separate P link. -/
def observer (adv : Observer Signal A) : R1Adv K CommitHandle Aux where
  prog := fun v log => adv.program (completed completion pubData env ⟨v,log⟩)
  decide := fun v => adv.decide (completed completion pubData env v)

def modelReal (adv : Observer Signal A) (w : (h).Instance) (r : (source).RealRand) :
    Signal × Observation A :=
  completed completion pubData env ((source).real h B outputs
    (observer completion pubData env adv) x w r)

/-- EXPERIMENTAL ideal experiment: unchanged simE followed by the public joint
trace/timing completion; the simulator produces the ordered failure prefixes
too. There is no witness argument to this experiment or its completion. -/
def ideal (adv : Observer Signal A) (r : (source).IdealRand) : Signal × Observation A :=
  completed completion pubData env ((source).ideal (simE (h).transport B outputs x)
    (observer completion pubData env adv) x r)

variable (native : Env → Observer Signal A → (h).Instance → R → NativeTrace A)
    (nativeSignal : Env → Observer Signal A → (h).Instance → R → Signal)

/-- EXPERIMENTAL real experiment: full native events survive failure,
divergence, panic and abort, rather than being reconstructed from Result. -/
def real (adv : Observer Signal A) (w : (h).Instance) (r : R) : Signal × Observation A :=
  observe (nativeSignal env adv w r) (native env adv w r)

def seedQueries (adv : Observer Signal A) (w : (h).Instance) :
    (source).RealRand → List ProverCommitSeedEvent19.Entry :=
  ProverCommitObserverQueries19.real W Pr 8
    (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs
    (ProverCommitReencode16.observer ProverCommitReencode16.encode
      (observer completion pubData env adv)) x w

/-- EXPERIMENTAL named links, not a proof of the native instance. cp is the
D163 common sample with EXACT QueryScan, seed and fuel coordinates. Every
field is ordinary proof work P; the existing trust list T is unchanged. -/
structure Links (adv : Observer Signal A) (w : (h).Instance) where
  cp : Coupling R (((source).RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape)
  context : Link_Context
    (fun s => ∃ i, ProverCommitFuelJoin22.bad
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (seedQueries template outputs x completion pubData env adv w) i (cp.toM s))
    (fun s => native env adv w (cp.toR s))
    (fun s => completion.complete pubData (completion.signal pubData env) env
      ((source).real h B outputs (observer completion pubData env adv) x w (cp.toM s).1.1))
  timing : Link_Timing
    (fun s => ∃ i, ProverCommitFuelJoin22.bad
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (seedQueries template outputs x completion pubData env adv w) i (cp.toM s))
    (fun s => native env adv w (cp.toR s))
    (fun s => completion.complete pubData (completion.signal pubData env) env
      ((source).real h B outputs (observer completion pubData env adv) x w (cp.toM s).1.1))
  signal : Link_Signal
    (fun s => ∃ i, ProverCommitFuelJoin22.bad
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (seedQueries template outputs x completion pubData env adv w) i (cp.toM s))
    (fun s => nativeSignal env adv w (cp.toR s))
    (fun _ => completion.signal pubData env)

/-- EXPERIMENTAL: the composed event join, conditional on three distinct links. -/
def joined (adv : Observer Signal A) (w : (h).Instance)
    (links : Links template outputs x completion pubData env native nativeSignal adv w) :
    ProverCommitFuelJoin22.RunJoin
      (real outputs env native nativeSignal adv w)
      (modelReal template outputs x completion pubData env adv w)
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (seedQueries template outputs x completion pubData env adv w) :=
  eventJoin _ _ _ _ _ _ links.cp links.context links.timing links.signal

/-- EXPERIMENTAL: definitionally the current deployed headline bound. -/
def bound : ℚ :=
  modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge

/-- EXPERIMENTAL, NOT ADOPTED: the SAME bound and numeric envelope as the
current headline, with no added timing term under exact joint timing links. -/
theorem draft_headline
    (links : ∀ (adv : Observer Signal A) (w : (h).Instance), (h).public w = x.1 →
      Links template outputs x completion pubData env native nativeSignal adv w) :
    (∀ (adv : Observer Signal A) (w : (h).Instance), (h).public w = x.1 →
      |mean (fun r => bit (adv.decide (real outputs env native nativeSignal adv w r))) -
        mean (fun r => bit (adv.decide (ideal template outputs x completion pubData env adv r)))| ≤
      bound template outputs x) ∧
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
      (joined template outputs x completion pubData env native nativeSignal adv w (links adv w hw))
      (fun run => bit (adv.decide run))
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
      (fun r => ProverCommitObserverQueries19.real_bound W Pr 8
        (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs _ x w r)
    have hscan : 8 * scanProbability ≤ 8 / (2 : ℚ)^486 := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left scan_probability_le (by norm_num : (0 : ℚ) ≤ 8)
    have hr := hr₀.trans (add_le_add (add_le_add
      ((ProverCommitModelCore16.real_bad_mass base h B outputs x seed hc₁ hc₂ w).trans
        (add_le_add (le_refl _) hscan)) (le_refl (ProverCommitSeedEvent19.budget (2^64)))) (le_refl ProverCommitFuelMass22.charge))
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
    have hmid := mid (observer completion pubData env adv) w hw
    have t₁ := abs_sub_le
      (mean (fun r => bit (adv.decide (real outputs env native nativeSignal adv w r))))
      (mean (realTest h B outputs source (observer completion pubData env adv) x w))
      (mean (idealTestS source (observer completion pubData env adv) x
        (simE (h).transport B outputs x)))
    have spare : (0 : ℚ) ≤ 8 / (2 : ℚ)^486 +
        ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge := by
      unfold ProverCommitSeedEvent19.budget ProverCommitFuelMass22.charge
      positivity
    calc _ ≤ (QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
          ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) +
          modelError W Pr L₁ L₂ := t₁.trans (add_le_add hr hmid)
         _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
          ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) +
          modelError W Pr L₁ L₂) +
          (8 / (2 : ℚ)^486 + ProverCommitSeedEvent19.budget (2^64) +
          ProverCommitFuelMass22.charge) := le_add_of_nonneg_right spare
         _ = modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 +
           QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) +
           2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge := by ring
         _ ≤ _ := add_le_add (add_le_add (add_le_add (le_refl _) hk) (le_refl _)) (le_refl _)

  · constructor
    · exact add_le_add (add_le_add model.2.1 (le_refl _)) (le_refl _)
    · apply (add_le_add (add_le_add model.2.1 (le_refl _)) (le_refl _)).trans_lt
      exact ProverCommitFuelMass22.total_lt_target
        (Nat.le_trans (Nat.add_le_add_right hM 1) (by norm_num)) (Nat.le_refl _)

#print axioms joined
#print axioms draft_headline
end PV_EVHD_Headline
