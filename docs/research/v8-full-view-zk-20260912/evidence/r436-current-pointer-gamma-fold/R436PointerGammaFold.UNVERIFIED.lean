import AspisV8R19.R432PointerPrimitive
import AspisV8R19.R184GammaBatchFold

/-! This is a composition of the counted-fold pointer-view model with the
closed gamma-fold model. It is not a native pointer/borrow, frame, dispatch, or
full Rust-fold correspondence, and it adds no Rust memory or execution premise. -/
set_option autoImplicit false
namespace AspisV8R19.R436PointerGammaFold

open Aeneas Aeneas.Std Result
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R184GammaBatchFold
open AspisV8R19.R164ProductExecution
open AspisV8R15.ExactTowerBase
open AspisR156FullFreeze.aspis_core

theorem counted_pointer_gamma_fold
    (heap : Heap field.QM31) (id : Nat) (a : Allocation field.QM31)
    (hlookup : heap id = some a)
    (start length : Nat)
    (hbound : start + length ≤ a.cells.length)
    (values : List QM31Exact)
    (hview : viewCells a start length = values.map R164ProductExecution.encode)
    (fallback : Result field.QM31)
    (power gamma acc : QM31Exact) :
    AspisV8R19.R193CountedSliceFoldControl.countedFold
      (loadForControl heap (backedPointer id a start) fallback)
      length closedGamma (R164ProductExecution.encode acc)
      (R164ProductExecution.encode power, R164ProductExecution.encode gamma) =
      .ok (R164ProductExecution.encode
        (acc + power * weightedSum values gamma)) := by
  rw [countedFold_pointer_view heap id a hlookup start length hbound fallback
    closedGamma (R164ProductExecution.encode acc)
    (R164ProductExecution.encode power, R164ProductExecution.encode gamma)]
  rw [hview]
  rw [closedGamma_foldMutList values power gamma acc]
  simp only [bind_tc_ok]
  rw [gammaFold_closed_form]

#print axioms counted_pointer_gamma_fold

end AspisV8R19.R436PointerGammaFold
