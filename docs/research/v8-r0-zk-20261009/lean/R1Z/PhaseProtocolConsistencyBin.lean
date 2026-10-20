import R1Z.PrivacyR1FinalProtocol

/-! A joint satisfiability check for the construction-owned hypotheses.
It does not supply Rust/source couplings, tape uniformity, or builder soundness.
The explicit finite residual data below witness a structural model; they are
not asserted to model the shipped tape/opening implementation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseProtocolConsistencyBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.PremisesR1PBin
  R1Z.PhaseProtocolInstanceBin R1Z.PhaseProtocolCoverageBin
local notation "K" => AspisWideTower.WideExact
variable {CommitHandle Aux : Type} {F : Subfield K}

/-- Only construction-owned checks. The residual source premises are not
hidden in this predicate. The phase interface itself supplies well-formedness. -/
def ConstructionChecks (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
    (seed : R1ProverP K CommitHandle Aux F (wire base publicWidth h B outputs x).toWire) : Prop :=
  RomGrammarBin.ReadCoverage (wire base publicWidth h B outputs x).toWire
    (prover base publicWidth h B outputs x seed).toProver publicWidth h B outputs x ∧
  PrivacyR1Final.RCommitSource (wire base publicWidth h B outputs x).toWire
    (prover base publicWidth h B outputs x seed).toProver ∧
  (∀ w : h.Instance, RCausal (wire base publicWidth h B outputs x).toWire
    (prover base publicWidth h B outputs x seed).toProver h B outputs x w) ∧
  (wire base publicWidth h B outputs x).toWire.qmax ≤ 2^64 ∧
  (∀ (w : h.Instance) (τ : Tape K F) (ch : Challenges K) (T : Fin 3) (u : Fib),
    ((prover base publicWidth h B outputs x seed).toProver.leafVal h w x τ ch T u).length =
      if T.val = 0 then 480 else 128) ∧
  PhaseLocalityBin.DecodeLocal (wire base publicWidth h B outputs x).toWire.dec ∧
  (rows01 base publicWidth h B outputs x).s1 =
    R1J.SamplerLawSpend.s1Spend (algebraMap R1J.SamplerLawSpend.QF K) ∧
  Function.Injective (algebraMap R1J.SamplerLawSpend.QF K)

theorem construction_checks (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
    (seed : R1ProverP K CommitHandle Aux F (wire base publicWidth h B outputs x).toWire)
    (hp : (base.pubBytes x).length ≤ publicWidth) :
    ConstructionChecks base publicWidth h B outputs x seed := by
  refine ⟨read_coverage base publicWidth h B outputs x seed hp,
    PrivacyR1FinalProtocol.commitment_grammar base publicWidth h B outputs x seed,
    ?_, Nat.le_refl _, ?_,
    (wire base publicWidth h B outputs x).decode_local,
    sampler_source base publicWidth h B outputs x, RingHom.injective _⟩
  · intro w
    exact (causal_iff _ _ _ _ _ _ w).mpr (causal_premise base publicWidth h B outputs x seed w)
  · intro w τ ch T u
    exact leaf_length B h w x τ ch T u

/-- An explicit finite residual wire: no assumed inhabitant of R1Wire. -/
def sampleBase (failure : ZkStatement.View K CommitHandle Aux R1Bat) :
    R1Wire K CommitHandle Aux where
  Cm := RIdx → OracleAnswer
  finCm := inferInstance
  neCm := inferInstance
  Tab := Unit
  finTab := inferInstance
  neTab := inferInstance
  look := fun _ _ => 0
  frame := PhaseMessageEncodingBin.frame PhaseMessageEncodingBin.wideBytes
  payload := PhaseMessageEncodingBin.payload PhaseMessageEncodingBin.wideBytes
  final := PhaseMessageEncodingBin.final PhaseMessageEncodingBin.wideBytes
  pubBytes := fun _ => []
  vtag := 0
  dec := PhaseSamplerParserBin.decode
  kstarOf := fun _ => 0
  comLog := fun _ _ _ _ => []
  failView := failure
  qmax := 0

/-- A residual seed exists at every constructed wire. Neither its arbitrary
zero counters nor its constant tape is claimed to satisfy the source joins. -/
def sampleSeed (W : R1Wire K CommitHandle Aux) : R1ProverP K CommitHandle Aux F W where
  E₁ := 0
  E₂ := 0
  caddr := fun _ _ _ _ _ _ _ _ _ => []
  leafVal := fun _ _ _ _ _ _ _ => []
  tapeOf := fun _ _ => some tape0
  openFib := fun _ _ => ∅
  openList := fun _ => []
  ord := PhaseScheduleBin.ord 0 0

/-- The construction-owned hypotheses are jointly inhabited with a genuine
witness of the statement, rather than an empty HonestProver.Instance.
This says nothing about satisfiability of the residual Rust/source joins. -/
theorem structural_hypotheses_inhabited
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (hw : h.public w = x.1) :
    ∃ (base : R1Wire K CommitHandle Aux)
      (seed : R1ProverP K CommitHandle Aux F (wire base 0 h B outputs x).toWire),
      ConstructionChecks base 0 h B outputs x seed ∧
      (∃ w' : h.Instance, h.public w' = x.1) := by
  let ch := PhaseSamplerParserBin.decode (fun _ => 0) (fun _ => 0) (fun _ => 0) 0
  let base := sampleBase (view h B outputs x w ch (tape0 : Tape K F))
  refine ⟨base, sampleSeed _, construction_checks base 0 h B outputs x (sampleSeed _) ?_, w, hw⟩
  exact Nat.le_refl 0

#print axioms construction_checks
#print axioms structural_hypotheses_inhabited
end R1Z.PhaseProtocolConsistencyBin
