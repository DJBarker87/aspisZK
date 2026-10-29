import CurrentClaimSumModel
import NEB_PureFrame
set_option autoImplicit false
namespace NEB_TraceFrame
open Aeneas Aeneas.Std Result

/-- All typed tags/indices and every raw eight-limb carrier are allowed.
The adopted deployed trace body ignores every argument; no observer premise. -/
theorem result {S Event : Type} (state : S) (tag : U16) (index : Usize)
    (x : AspisR1CurrentPreparedClaim.aspis_core.field.WideExact) :
    AspisR1CurrentPreparedClaim.trace.value tag index x=ok () ∧
    NEB_PureFrame.run (Event:=Event) state
      (AspisR1CurrentPreparedClaim.trace.value tag index x)=ok ((),state,[]) := by
  exact ⟨rfl,rfl⟩

#print axioms result
end NEB_TraceFrame
