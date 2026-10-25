import Hiq_RouteHead
import Hiq_RuntimeAction
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_LifecycleRejection
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry Hiq_RuntimeAction

theorem rejected (data : Slice U8) (tag : U8)
    (lifecycle : tag = 1#u8 ∨ tag = 2#u8 ∨ tag = 4#u8 ∨ tag = 5#u8 ∨ tag = 6#u8)
    (head : data.val.head? = some tag) : Hiq_ReleaseRoute.route data = .reject := by
  apply Hiq_RouteHead.reject_other data tag head
  · rcases lifecycle with h | h | h | h | h <;> subst tag <;> decide
  · rcases lifecycle with h | h | h | h | h <;> subst tag <;> decide

theorem rollback (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (layout : Layout) (data : Slice U8) (tag : U8)
    (lifecycle : tag = 1#u8 ∨ tag = 2#u8 ∨ tag = 4#u8 ∨ tag = 5#u8 ∨ tag = 6#u8)
    (head : data.val.head? = some tag) :
    Hiq_RuntimeAction.apply ops id store (.invoke layout data) = (store,.rollback) := by
  simp only [Hiq_RuntimeAction.apply,rejected data tag lifecycle head]

#print axioms rejected
#print axioms rollback
end AspisR1.Hiq_LifecycleRejection
end
