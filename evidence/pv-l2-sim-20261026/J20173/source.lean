import R1Z.PV_L2_F3Tape
import R1Z.ProverCommitQuotientCoupling
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3CompletionLaw
open R0Z.JointView R1Z.ProverCommitTapeCompletion R1Z.CouplingR1PBin
variable {K : Type} [Field K] [Fintype K] {F : Subfield K}

theorem padding_uniform : MP (padding (K := K) (F := F)) := by
  have h := mp_comp (mp_equiv (completionEquiv (K := K) (F := F)).symm)
    (mp_snd (X := SourceTape K F) (Y := Padding K F))
  exact h

theorem complete_uniform : MP (fun p : SourceTape K F × Tape K F => complete p.1 (padding p.2)) := by
  have h := mp_comp (mp_prodMap (mp_equiv (Equiv.refl (SourceTape K F)))
    (padding_uniform (K := K) (F := F))) (mp_equiv (completionEquiv (K := K) (F := F)))
  exact h

#print axioms padding_uniform
#print axioms complete_uniform
end R1Z.PV_L2_F3CompletionLaw
