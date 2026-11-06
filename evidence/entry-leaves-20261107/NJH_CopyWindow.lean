import NJH_Ref.Funs
set_option autoImplicit false
namespace NJH_CopyWindow
open Aeneas Aeneas.Std Result
theorem selected (old new : U8) (i : Usize) :
    NJH_Ref.copy_window_ref old new i i = ok new := by
  simp [NJH_Ref.copy_window_ref]
theorem frame (old new : U8) (i j : Usize) (h : i ≠ j) :
    NJH_Ref.copy_window_ref old new i j = ok old := by
  simp [NJH_Ref.copy_window_ref, h]
/-- Arbitrary-coordinate extensional composition: no whole-buffer reduction. -/
theorem extensional {I : Type} (pre src post : I → U8) (written : I → Prop)
    [DecidablePred written]
    (step : ∀ i, post i = if written i then src i else pre i) :
    post = fun i => if written i then src i else pre i := funext step
#print axioms selected
#print axioms frame
#print axioms extensional
end NJH_CopyWindow
