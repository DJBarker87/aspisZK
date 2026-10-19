import AspisR1BatchedWeightsExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchedWeightsPushBodyStepV7
open AspisR1BatchedWeightsExtraction
abbrev BW := batched_weights.BatchedWeights
abbrev Range := core.ops.range.Range Usize
abbrev Raw := alloc.vec.Vec (Array Std.U64 4#usize)
theorem push_body_step
    (index : Usize) (limbs : Array Std.U32 4#usize) (iter : Range)
    (self : BW) (basis : aspis_core.field.M31)
    (j : Usize) (iterNext : Range) (limb : Std.U32) (limb64 basis64 product : Std.U64)
    (old : Array Std.U64 4#usize) (previous sum : Std.U64)
    (updated : Array Std.U64 4#usize)
    (back : Array Std.U64 4#usize → Raw)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some j, iterNext))
    (hlimb : Array.index_usize limbs j = .ok limb)
    (hlimb64 : lift (core.convert.num.FromU64U32.from limb) = .ok limb64)
    (hbasis64 : lift (core.convert.num.FromU64U32.from basis) = .ok basis64)
    (hmul : (limb64 * basis64 : Result Std.U64) = .ok product)
    (hvec : alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize))
      self.raw index = .ok (old, back))
    (hread : Array.index_usize old j = .ok previous)
    (hadd : (previous + product : Result Std.U64) = .ok sum)
    (hupdate : Array.update old j sum = .ok updated) :
    batched_weights.BatchedWeights.push_loop.body index limbs iter self basis =
      .ok (.cont (iterNext, { self with raw := back updated }, basis)) := by
  simp [batched_weights.BatchedWeights.push_loop.body, hnext, bind_tc_ok,
    hlimb, hlimb64, hbasis64, hmul, hvec, hread, hadd, hupdate]
#print axioms push_body_step
end AspisR1BatchedWeightsPushBodyStepV7
