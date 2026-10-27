import R1Z.PV_CB_ProducerPost
set_option autoImplicit false
namespace R1Z.PV_CB_ReachBind
open Aeneas Aeneas.Std Result

theorem congr {A B : Type} (run : Result A) (left right : A → Result B)
    (agree : ∀ value, run = ok value → left value = right value) :
    (do let value ← run; left value) = (do let value ← run; right value) := by
  cases run with
  | ok value => exact agree value rfl
  | fail err => rfl
  | div => rfl
#print axioms congr
end R1Z.PV_CB_ReachBind
