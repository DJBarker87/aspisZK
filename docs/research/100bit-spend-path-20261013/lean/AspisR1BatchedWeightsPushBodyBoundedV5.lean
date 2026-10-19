import AspisR1BatchedWeightsPushBodyBoundedV4
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchedWeightsPushBodyBoundedV5
open AspisR1BatchedWeightsExtraction
abbrev BW := batched_weights.BatchedWeights
abbrev Range := core.ops.range.Range Usize
abbrev Raw := alloc.vec.Vec (Array Std.U64 4#usize)

private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

/-- The fixed four-element limb buffer read in the actual generated body is
total whenever the range index is below four.  The remaining vector and raw
lane bounds are left explicit for the caller's state invariant. -/
theorem push_body_step_bounded_of_reads
    (index : Usize) (limbs : Array Std.U32 4#usize) (iter : Range)
    (self : BW) (basis : aspis_core.field.M31) (j : Usize) (iterNext : Range)
    (old : Array Std.U64 4#usize)
    (back : Array Std.U64 4#usize → Raw) (previous : Std.U64)
    (terms : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some j, iterNext))
    (hj : j.val < 4)
    (hlimbBound : (limbs.val[j.val]'(by simpa [limbs.property] using hj)).val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hvec : alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize))
      self.raw index = .ok (old, back))
    (hraw : previous.val < 2^34 + (terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (hread : Array.index_usize old j = .ok previous) :
    ∃ product : Std.U64, ∃ updated : Array Std.U64 4#usize,
      ((limbs.val[j.val]'(by simpa [limbs.property] using hj)).val * basis.val) = product.val ∧
      batched_weights.BatchedWeights.push_loop.body index limbs iter self basis =
        .ok (.cont (iterNext, { self with raw := back updated }, basis)) := by
  let limb := limbs.val[j.val]'(by simpa [limbs.property] using hj)
  have hlimbRead : Array.index_usize limbs j = .ok limb :=
    index_usize_ok limbs j (by simpa [limbs.property] using hj)
  obtain ⟨product, updated, hproduct, hbody⟩ :=
    AspisR1BatchedWeightsPushBodyBoundedV4.push_body_step_bounded
      index limbs iter self basis j iterNext limb old back previous terms
      hnext hj hlimbRead hlimbBound hbasis hvec hraw hread
  exact ⟨product, updated, hproduct, hbody⟩
#print axioms push_body_step_bounded_of_reads
end AspisR1BatchedWeightsPushBodyBoundedV5
