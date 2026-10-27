import R1Z.PV_L2_F3Pair
import R1Z.ProverCommitOwnedCallerLaw

/-! Actual owned decoder quotient paired with both complete scalar-count
arrays. Failure is unchanged; a source failure-prefix observation still needs
the existing exhaustion event or its independent source-prefix join. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3Tape
open R0Z R0Z.JointView R1Z.ProverCommitSourceDecoder R1Z.ProverCommitWordCarrier
  R1Z.ProverCommitTapeCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sourceBase L₁ L₂ E₁ E₂ arrayCarrierEquiv
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)
abbrev History := (Fin L₁ → Nat) × (Fin L₂ → Nat)

def outputEquiv : (((Fin L₁ → F) × (Fin L₂ → F)) × History) ≃ (SourceTape K F × History) :=
  Equiv.prodCongr (arrayCarrierEquiv (K := K)) (Equiv.refl History)

def observed (input : Inputs) : Option (SourceTape K F × History) :=
  (PV_L2_F3Pair.pair E₁ E₂ L₁ L₂ input).map (outputEquiv (K := K))

theorem quotient_erases (input : Inputs) :
    (observed (K := K) input).map Prod.fst = quotientDecoder (K := K) input := by
  change ((PV_L2_F3Pair.pair E₁ E₂ L₁ L₂ input).map (outputEquiv (K := K))).map Prod.fst = _
  simp only [Option.map_map]
  change (PV_L2_F3Pair.pair E₁ E₂ L₁ L₂ input).map
    ((arrayCarrierEquiv (K := K)) ∘ Prod.fst) = _
  rw [← Option.map_map,PV_L2_F3Pair.pair_erases]
  rfl

/-- Joins the history-aware decoder to the endpoint's ACTUAL owned tapeOf. -/
theorem owned_erases (input : Inputs) :
    (observed (K := K) input).map Prod.fst =
      (ProverCommitOwnedDecoder.decoder (K := K) input.1 input.2).map project := by
  rw [quotient_erases]
  exact (ProverCommitOwnedDecoder.quotient_decoder input).symm

theorem observed_fibres (a b : SourceTape K F) (history : History) :
    (Finset.univ.filter (fun input => observed (K := K) input = some (a,history))).card =
      (Finset.univ.filter (fun input => observed (K := K) input = some (b,history))).card := by
  have heq (out : SourceTape K F × History) :
      (Finset.univ.filter (fun input => observed (K := K) input = some out)) =
        Finset.univ.filter (fun input => PV_L2_F3Pair.pair E₁ E₂ L₁ L₂ input =
          some ((outputEquiv (K := K)).symm out)) := by
    ext input
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,observed]
    exact map_equiv_some (outputEquiv (K := K)) _ out
  rw [heq,heq]
  change (Finset.univ.filter (fun input => PV_L2_F3Pair.pair E₁ E₂ L₁ L₂ input =
    some (((arrayCarrierEquiv (K := K)).symm a),history))).card =
    (Finset.univ.filter (fun input => PV_L2_F3Pair.pair E₁ E₂ L₁ L₂ input =
    some (((arrayCarrierEquiv (K := K)).symm b),history))).card
  convert PV_L2_F3Pair.pair_fibres E₁ E₂ L₁ L₂
    ((arrayCarrierEquiv (K := K)).symm a).1 ((arrayCarrierEquiv (K := K)).symm b).1
    ((arrayCarrierEquiv (K := K)).symm a).2 ((arrayCarrierEquiv (K := K)).symm b).2
    history using 1 <;> apply congrArg Finset.card <;> ext input <;>
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem owned_joint_law (e : History → SourceTape K F ≃ SourceTape K F) :
    EqualLaws (fun input => (observed (K := K) input).map (fun p => (e p.2 p.1,p.2)))
      (observed (K := K)) := by
  apply PV_L2_F3Law.conditional_relabel
  intro history a b
  convert observed_fibres (K := K) a b history using 1 <;>
    apply congrArg Finset.card <;> ext input <;>
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]

#print axioms outputEquiv
#print axioms quotient_erases
#print axioms owned_erases
#print axioms observed_fibres
#print axioms owned_joint_law
end R1Z.PV_L2_F3Tape
