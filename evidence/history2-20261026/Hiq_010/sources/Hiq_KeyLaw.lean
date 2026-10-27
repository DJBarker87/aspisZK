import Hist_CausalBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_KeyLaw
open Aeneas Aeneas.Std Result

theorem installed_eq (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq) :
    Hist_Authority.install ops = ops := by
  cases ops
  cases law
  rfl

/-- Expose precisely the remaining pure library leaf, rather than silently
changing the installed DrvC dictionary. -/
theorem owner (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (id : S2W_ExtractionBoundary.Program) (store : Hist_Store.Store)
    (layout : Hist_RuntimeEntry.Layout) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops id
      (Hist_RuntimeEntry.load store layout).first data = ok (.Ok saved)) :
    (store (layout.handles 2).1).owner = id := by
  apply Hist_RuntimeEntry.accepted_owner ops id store layout data saved
  simpa only [installed_eq ops law] using accepted

#print axioms installed_eq
#print axioms owner
end AspisR1.Hiq_KeyLaw
end
