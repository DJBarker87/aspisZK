import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_IfLaws
open Aeneas.Std ProverRwFull PV_W_TypedEffects
variable [ExternalTypes]

theorem erase_if_congr {A : Type} (ops : ExternalFuns) (p : Prop) [Decidable p]
    (yes no : P A) (left right : Aeneas.Std.Result A)
    (hy : erase ops yes = left) (hn : erase ops no = right) :
    erase ops (if p then yes else no) = if p then left else right := by
  rw [PV_W_RecursiveLaws.erase_ite,hy,hn]

#print axioms erase_if_congr
end R1Z.PV_W_IfLaws
