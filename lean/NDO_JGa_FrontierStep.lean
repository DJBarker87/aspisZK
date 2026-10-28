import NDO_JGa_EmptyRoot
import NDO_JGa_DigestLoop
import RPv_FIy_FrontierStep
import NDO_JFy_FrontierCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_FrontierStep
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open FIy_FrontierStep (Selectors Snapshot)

@[step] theorem source (level : Usize) (a : Array field.QM31 16#usize) (s : Selectors)
    (d : Array field.QM31 8#usize) (src : Snapshot) (hi : level.val<20)
    (ha : canonical a) (hd : canonical d) (hh : canonical s.high) (hl : canonical s.low)
    (hf : ∀ row∈src.frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P) :
    FIy_FrontierStep.run level a s d src ⦃ out => canonical out ⦄ := by
  unfold FIy_FrontierStep.run poseidon2.RATE
  step*
  all_goals first | assumption | scalar_tac | (subst_vars; exact hf _ (List.getElem_mem (by rw [src.frontier.property];exact hi)))
#print axioms source
end AspisR1.JGa_FrontierStep
end
