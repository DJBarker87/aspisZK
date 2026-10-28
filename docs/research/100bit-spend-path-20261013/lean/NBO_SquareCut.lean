import NBO_QueryRhs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace NBO_SquareCut
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Exact reached line and geometry prefix before scalar multiplication. -/
def before (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (values : Array Stage2E 4#usize)
 (inverse : Array U32 5#usize) : Result (Stage2E × U32) := do
  let we6 ← Array.index_usize p.alpha 1#usize
  let folded1 ← ops.op16 we6 values inverse
  let i10 ← lift (Std.Usize.wrapping_mul 2#usize a.next)
  let i11 ← lift (Std.Usize.wrapping_add i10 1#usize)
  ops.op15 10#u16 i11 folded1
  let i12 ← lift (Std.Usize.wrapping_sub a.next geometry.start)
  let z ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.M31) geometry.line_z i12
  ok (folded1,z)
/-- Exact emitted continuation AFTER the SAME scalar multiply returns.
The value m is a reached child return; no arithmetic is silently replaced. -/
def after (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (pending : verifier.BatchedWeights)
 (folded1 : Stage2E) (m : U32) :
 Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error) := do
  let m1 ← ops.op8 m
  let m2 ← ops.op5
  let node ← ops.op6 m1 m2
  let (a1, pending1) ←
    (verifier.accumulate_batched_with_node ops) p a node folded1 pending
  ops.op19 obs (verifier.Phase.Query a.next)
  ok (core.result.Result.Ok (a1, pending1))
private theorem associate {A B C : Type} (x : Result A) (f : A → Result B)
 (g : B → Result C) : ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
 cases x <;> rfl
/-- Total Result fission at the actual pure field-call boundary. -/
theorem association (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (values : Array Stage2E 4#usize)
 (inverse : Array U32 5#usize) :
 NBO_QueryFactor.suffix ops p a obs geometry pending values inverse =
 (do let (line,z) ← before ops p a geometry values inverse
     let square ← ops.op7 z z
     after ops p a obs pending line square) := by
 unfold NBO_QueryFactor.suffix before after
 simp only [associate,bind_tc_ok]
 rfl
#print axioms associate
#print axioms association
end NBO_SquareCut
end
