import PV_L1_Logged
set_option autoImplicit false
namespace PV_L1_EraseIf
open PV_L1_Logged
theorem erase_if {A : Type} (p : Prop) [Decidable p] (a b : Logged A) :
    erase (if p then a else b) = if p then erase a else erase b := by
  split <;> rfl
#print axioms erase_if
end PV_L1_EraseIf
