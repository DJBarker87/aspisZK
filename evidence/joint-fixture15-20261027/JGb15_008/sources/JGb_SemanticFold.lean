import JGb_Horner
import JGb_Challenges
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_SemanticFold
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (prepared)
open FIw_ArrayValue (canonical)

/-- First composition fold on the actual semantic coefficient array and copy
residual. No Poseidon call or output is assumed for this independent prefix. -/
theorem source (sem : Array field.QM31 24#usize) (seed : field.QM31)
    (hsem : canonical sem) (hs : Canon seed) :
    ∃ p mid,field.PreparedQm31Multiplier.new JFu_TerminalPrefix.challenges.theta=ok p ∧
      ExtractedMaskPreparedState.PreparedFor (prepared p)
        (FIv_NativeArithmetic.qm JFu_TerminalPrefix.challenges.theta) ∧
      pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 ⟨sem.val⟩ p seed=ok mid ∧
      Canon mid ∧ decode mid=FIv_Horner24.model (decode JFu_TerminalPrefix.challenges.theta)
        sem.val.reverse (decode seed) := by
  obtain ⟨p,hp,hpv⟩ := FIv_PreparedNewTotal.value _ JGb_Challenges.theta
  obtain ⟨mid,hm,hmc,hmv⟩ := FIv_HornerTotal.value sem.val.reverse p _ seed
    JGb_Challenges.theta hs hpv (fun x hx => hsem x (List.mem_reverse.mp hx))
  simp only [List.reverse_reverse] at hm
  exact ⟨p,mid,hp,hpv,hm,hmc,hmv⟩
#print axioms source
end AspisR1.JGb_SemanticFold
end
