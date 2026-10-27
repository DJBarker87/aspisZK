import RPt_JFo_Powers
import RPt_FIo_WideValues
import SAQ_WideABI
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_Powers
open Aeneas Aeneas.Std Result

def value : Array Tx2N_Powers.E 29#usize := Classical.choose JFo_Powers.source

theorem source : Tx2N_Powers.powers 29#usize JFo_Prepared.value.gamma=ok value :=
  (Classical.choose_spec JFo_Powers.source).1

theorem canonical (j : Fin 29) :
    FIo_WideValues.Canon (FIo_Install.toE (value.val[j.val]'(by rw [value.property];exact j.isLt))) := by
  have h := ((Classical.choose_spec JFo_Powers.source).2 j).1
  change ((_ ∧ _) ∧ (_ ∧ _)) ∧ ((_ ∧ _) ∧ (_ ∧ _)) at h
  exact h

#print axioms source
#print axioms canonical
end AspisR1.JFr_TX2_Powers
end
