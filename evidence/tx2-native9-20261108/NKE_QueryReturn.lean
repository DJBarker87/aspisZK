import NJR_Cuts
import NJU_CommonObserved
set_option autoImplicit false
noncomputable section
namespace NKE_QueryReturn
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
abbrev Reply := core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error
abbrev Post := core.result.Result
 (alloc.vec.Vec aspis_core.field.QM31 × aspis_core.field.wide_exact.WideExact ×
  aspis_core.field.QM31 × Usize × verifier.BatchedWeights) verifier.Error
/-- Native destructuring is total on the full Rust Result, not success-only. -/
def G : Reply → Post
 | .Err e => .Err e
 | .Ok (a,b) => .Ok (a.weights,a.rhs,a.power,a.next,b)

def source : Post → Reply
 | .Err e => .Err e
 | .Ok (weights,rhs,power,next,pending) => .Ok (⟨weights,rhs,power,next⟩,pending)

theorem cut (reply : Reply) : NJR_Cuts.queryReturn reply (G reply) := by
 cases reply <;> rfl

theorem complete (reply : Reply) : source (G reply)=reply := by
 cases reply with
 | Err e => rfl
 | Ok pair => rcases pair with ⟨⟨weights,rhs,power,next⟩,pending⟩;rfl

/-- At the actual query event no second reply is selected. Outer fail/div
remain exactly where the entered child emitted them. -/
def observed (reply : Result Reply) : Result Reply := do
 let value ← reply
 ok (source (G value))

theorem observed_exact (reply : Result Reply) : observed reply=reply := by
 cases reply with
 | fail e => rfl
 | div => rfl
 | ok value => exact congrArg Result.ok (complete value)

#print axioms cut
#print axioms complete
#print axioms observed_exact
end NKE_QueryReturn
