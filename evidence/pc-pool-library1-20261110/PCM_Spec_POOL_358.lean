import PCM_Rejection
import PCM_StepLaws
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_358
open RSL PCM PCM.Computation
abbrev Args := AccountInfo × AccountInfo × AccountInfo × Nat × B32 × List Bytes
structure Children where
  rentGet : Child Unit PCM.Rent
  withRent : Child (Args × PCM.Rent) Unit
/-- Rent::get is reached before the with-rent helper. No successful CPI,
rent exemption, system semantics, or runtime borrow frame is assumed. -/
def Ref (C : Children) (a : Args) : Computation Unit := do
  let rent ← C.rentGet.call ()
  C.withRent.call (a,rent)
def RowSpec (C : Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error (C : Children) (a : Args)
    (early : C.rentGet.call () = PCM.Computation.throw (.unsupportedSysvar)) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref C) a (.unsupportedSysvar) .invalidArgument trivial
  · unfold Ref
    rw [early]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_358
