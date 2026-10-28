import NBO_Enumerate
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace NBO_QueryFactor
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev Cut := Stage2E × Array Stage2E 4#usize × Array U32 5#usize
/-- Exact emitted prefix; only a.next is projected before entering. -/
def prefix (ops : Ops) (proof : Slice U8) (p : verifier.Prepared) (next : Usize)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry) :
 Result (core.result.Result Cut verifier.Error) := do
  let i ← Array.index_usize p.queries next
  let u ← lift (UScalar.cast .Usize i)
  let q ← ops.op11 proof next
  let dots ← ops.op20 q g
  let i1 ← lift (Std.Usize.wrapping_mul 4#usize next)
  let we ← Array.index_usize dots 0#usize
  ops.op15 9#u16 i1 we
  let i2 ← lift (Std.Usize.wrapping_mul 4#usize next)
  let i3 ← lift (Std.Usize.wrapping_add i2 1#usize)
  let we1 ← Array.index_usize dots 1#usize
  ops.op15 9#u16 i3 we1
  let i4 ← lift (Std.Usize.wrapping_mul 4#usize next)
  let i5 ← lift (Std.Usize.wrapping_add i4 2#usize)
  let we2 ← Array.index_usize dots 2#usize
  ops.op15 9#u16 i5 we2
  let i6 ← lift (Std.Usize.wrapping_mul 4#usize next)
  let i7 ← lift (Std.Usize.wrapping_add i6 3#usize)
  let we3 ← Array.index_usize dots 3#usize
  ops.op15 9#u16 i7 we3
  let inverse ← ops.op18 geometry next
  let we4 ← Array.index_usize p.alpha 0#usize
  let folded ← ops.op17 we4 dots inverse
  let i8 ← lift (Std.Usize.wrapping_mul 2#usize next)
  ops.op15 10#u16 i8 folded
  let values ←
    ops.op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact ops)
      q
  let i9 ← u % 4#usize
  let we5 ← Array.index_usize values i9
  let b ←
    core.cmp.PartialEq.ne.trait_default
      ops.widePartialEq
      folded we5
  if b then ok (.Err verifier.Error.Query)
  else ok (.Ok (folded,values,inverse))
/-- Exact emitted accepted continuation, including the actual accumulation
body and mark. No child output is supplied independently. -/
def suffix (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (values : Array Stage2E 4#usize)
 (inverse : Array U32 5#usize) :
 Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error) := do
  let we6 ← Array.index_usize p.alpha 1#usize
  let folded1 ← ops.op16 we6 values inverse
  let i10 ← lift (Std.Usize.wrapping_mul 2#usize a.next)
  let i11 ← lift (Std.Usize.wrapping_add i10 1#usize)
  ops.op15 10#u16 i11 folded1
  let i12 ← lift (Std.Usize.wrapping_sub a.next geometry.start)
  let z ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.M31) geometry.line_z i12
  let m ← ops.op7 z z
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
private theorem branch {A B : Type} (b : Bool) (x y : Result A) (f : A → Result B) :
 ((if b then x else y) >>= f) = (if b then x >>= f else y >>= f) := by
 cases b <;> rfl
/-- Total Result equality, including rejected prefixes and divergence.
It factors the actual emitted function, not a selected successful output. -/
theorem association (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) :
 verifier.candidate.query_values ops proof p a g obs geometry pending =
 (do let cut ← prefix ops proof p a.next g geometry
     match cut with
     | .Err error => ok (.Err error)
     | .Ok (_,values,inverse) => suffix ops p a obs geometry pending values inverse) := by
 unfold verifier.candidate.query_values prefix suffix
 simp only [associate,branch,bind_tc_ok]
#print axioms associate
#print axioms branch
#print axioms association
end NBO_QueryFactor
end
