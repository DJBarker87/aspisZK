import R1Z.PhaseRefinementObstructionBin
import R1Z.RomGrammarBin

/-! The final endpoint fixes only the ROM backend, not the protocol encoder.
Its universally quantified base still admits the premature-C2 counterexample.
Consequently its causal premise cannot be discharged by a universal phase
wrapper. This does not rule out a separately identified concrete protocol. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseEndpointObstructionBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1
  R1Z.PhaseLocalityBin R1Z.CausalOrderObstructionBin R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.TranscriptR1

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem endpoint_prematureC2_excluded (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (W : R1PhaseWire h B outputs x)
    (hw : W.toWire = RomFiniteBin.wire (prematureC2 base) (RomGrammarBin.bound publicWidth)) :
    False := by
  apply PhaseRefinementObstructionBin.prematureC2_excluded h B outputs x w
    (RomFiniteBin.wire base (RomGrammarBin.bound publicWidth)) W
  exact hw

theorem no_universal_endpoint_refinement (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ) :
    ¬ (∀ wire : R1Wire K CommitHandle Aux, ∃ W : R1PhaseWire h B outputs x,
      W.toWire = RomFiniteBin.wire wire (RomGrammarBin.bound publicWidth)) := by
  intro all
  obtain ⟨W, hw⟩ := all (prematureC2 base)
  exact endpoint_prematureC2_excluded h B outputs x w base publicWidth W hw

theorem endpoint_prematureC2_not_causal
    (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (Pr : R1ProverP K CommitHandle Aux F
      (RomFiniteBin.wire (prematureC2 base) (RomGrammarBin.bound publicWidth)))
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (late : ¬ Pr.ord.symm (.inr (.inl 1)) < Pr.ord.symm (.inl (.absS 0))) :
    ¬ RCausal (RomFiniteBin.wire (prematureC2 base) (RomGrammarBin.bound publicWidth))
      Pr h B outputs x w :=
  prematureC2_not_causal (RomFiniteBin.wire base (RomGrammarBin.bound publicWidth))
    Pr h B outputs x w late

#print axioms endpoint_prematureC2_not_causal
#print axioms endpoint_prematureC2_excluded
#print axioms no_universal_endpoint_refinement
end R1Z.PhaseEndpointObstructionBin
