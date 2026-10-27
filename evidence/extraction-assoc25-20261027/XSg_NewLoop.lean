import XSg_NewStep
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XSg_NewLoop
open XSg_NewRows XRu_NewStep
/-- The actual arbitrary-length constructor loop equals the map of its SAME
input weights. This proof is an invariant induction, not concrete reduction. -/
theorem source (weights : Slice Q) (raw out : Raw) (index : Usize)
 (inv : Inv weights (raw,index)) (built : Built weights raw index.val)
 (run : verifier.BatchedWeights.new_loop weights raw index=ok out) :
 out.val=weights.val.map row := by
 unfold verifier.BatchedWeights.new_loop at run
 apply XRl_LoopInvariant.preserve _
  (fun s : S => Inv weights s ∧ Built weights s.1 s.2.val)
  (fun out => out.val=weights.val.map row) (measure weights) ?_ (raw,index) out ⟨inv,built⟩ run
 intro s r hs hr
 have shape := XRu_NewStep.source weights s r hs.1 hr
 have value := XSg_NewStep.source weights s r hs.1 hs.2 hr
 cases r with
 | done out => exact value
 | cont next => exact ⟨⟨shape.1,value⟩,shape.2⟩
#print axioms source
end XSg_NewLoop
