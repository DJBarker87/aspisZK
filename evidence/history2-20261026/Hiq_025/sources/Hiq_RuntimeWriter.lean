import Hiq_ReleaseRoute
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_RuntimeWriter
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry

def apply (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (layout : Layout) (data : Slice U8) : Store × S2X.AccountEvent :=
  match AdapterRw.r1_pool_adapter.owned.stage1_owned ops id (load store layout).first data with
  | .ok (.Ok saved) => (commit store (layout.handles 2).1 saved,
      .committedWrite (layout.handles 2).1 (MultiproofConeCanonical.bytesOf saved.val))
  | _ => (store,.rollback)

theorem classified (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (id : S2W_ExtractionBoundary.Program) (store : Store) (layout : Layout) (data : Slice U8) :
    Step ops id store (apply ops id store layout data).2 (apply ops id store layout data).1 := by
  unfold apply
  cases h : AdapterRw.r1_pool_adapter.owned.stage1_owned ops id (load store layout).first data with
  | fail e => exact Step.rollback store
  | div => exact Step.rollback store
  | ok reply => cases reply with
    | Err e => exact Step.rollback store
    | Ok saved =>
      exact Step.first store (layout.handles 2).1 (load store layout) data saved rfl
        (Hiq_KeyLaw.owner ops keyLaw id store layout data saved h) h

#print axioms classified
end AspisR1.Hiq_RuntimeWriter
end
