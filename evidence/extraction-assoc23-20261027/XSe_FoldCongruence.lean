import XSe_ListDriver
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_FoldCongruence
/-- Only source-selected stages need equality; arbitrary state and errors are
retained by the same generic short-circuit fold. -/
theorem source {I S E : Type} (left right : I → S → Result (core.result.Result S E))
 (items : List I) (same : ∀ i∈items, ∀ s, left i s=right i s)
 (state : core.result.Result S E) :
 XSe_ListDriver.fold left items state=XSe_ListDriver.fold right items state := by
 induction items generalizing state with
 | nil => rfl
 | cons item rest ih =>
   cases state with
   | Err e => rfl
   | Ok s =>
     simp only [XSe_ListDriver.fold]
     rw [same item (by simp) s]
     congr 1
     funext next
     exact ih (fun i hi => same i (by simp [hi])) next
#print axioms source
end XSe_FoldCongruence
