import XRk_Funs
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRl_Adapter
abbrev Capture := sampler.low_base_p_digits.closure_1
abbrev emittedMut := sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
abbrev emittedOnce := sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
abbrev traitMut := sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32
abbrev traitOnce := sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
/-- Explicit original mutable closure borrow semantics: apply the emitted
backward function to the returned capture. Rust sampler.rs:59-67 mutates
quotient, whose eight words remain live after the call. -/
def originalClosureMut (c : Capture) (i : Usize) : Result (U32 × Capture) := do
  let (v,last,restore) ← emittedMut c i
  ok (v,restore last)

theorem closure_1_FnMut (c : Capture) (i : Usize) :
    traitMut.call_mut c i = originalClosureMut c i := by rfl

/-- FnOnce's fixed trait ABI has no capture result. This is only the scalar
projection, not an equality of final borrowed capture states. -/
def eraseCapture : Result (U32 × Capture) → Result U32
  | .ok (v,_) => .ok v
  | .fail e => .fail e
  | .div => .div

theorem closure_1_FnOnce_projection (c : Capture) (i : Usize) :
    traitOnce.call_once c i = eraseCapture (emittedOnce c i) := by
  change (do let (v,_) ← emittedOnce c i; ok v) = _
  cases emittedOnce c i with
  | fail e => rfl
  | div => rfl
  | ok r => rcases r with ⟨v,last⟩; rfl

/-- No final state is erased by call_mut; returned errors and divergence are
also identical to the direct emitted call_once's state-restoring semantics. -/
theorem closure_1_mut_once (c : Capture) (i : Usize) :
    traitMut.call_mut c i = emittedOnce c i := by rfl

#print axioms closure_1_FnMut
#print axioms closure_1_FnOnce_projection
#print axioms closure_1_mut_once
end XRl_Adapter
