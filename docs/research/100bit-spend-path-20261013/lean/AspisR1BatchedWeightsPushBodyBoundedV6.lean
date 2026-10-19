import AspisR1BatchedWeightsPushBodyBoundedV5
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1BatchedWeightsPushBodyBoundedV6
open AspisR1BatchedWeightsExtraction
abbrev BW := batched_weights.BatchedWeights
abbrev Range := core.ops.range.Range Usize
abbrev Raw := alloc.vec.Vec (Array Std.U64 4#usize)

/-- The one-step update is total at an in-range raw-vector index and an
in-range lane, provided the selected old lane satisfies the cadence bound. -/
theorem push_body_step_bounded_of_state
    (index : Usize) (limbs : Array Std.U32 4#usize) (iter : Range)
    (self : BW) (basis : aspis_core.field.M31) (j : Usize) (iterNext : Range)
    (terms : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some j, iterNext))
    (hj : j.val < 4)
    (hlimbBound : (limbs.val[j.val]'(by simpa [limbs.property] using hj)).val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hindex : index.val < self.raw.length)
    (hrawAt : ∀ (old : Array Std.U64 4#usize),
      old = self.raw.val[index.val]'(by simpa using hindex) →
      ∀ (k : Nat) (hk : k < 4),
        (old.val[k]'(by simpa [old.property] using hk)).val <
          2^34 + (terms.val % 4) * AspisR1BatchedAllPrefix.cap) :
    ∃ product : Std.U64, ∃ updated : Array Std.U64 4#usize,
    ∃ back : Array Std.U64 4#usize → Raw,
      ((limbs.val[j.val]'(by simpa [limbs.property] using hj)).val * basis.val) = product.val ∧
      batched_weights.BatchedWeights.push_loop.body index limbs iter self basis =
        .ok (.cont (iterNext, { self with raw := back updated }, basis)) := by
  have h4 : (4#usize).val = 4 := by decide
  have hjArray : j.val < (4#usize).val := by simpa [h4] using hj
  obtain ⟨⟨old, back⟩, hmut, _hold, hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec self.raw index hindex)
  have hvec : alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize))
      self.raw index = .ok (old, back) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hmut
  have hraw : (old.val[j.val]'(by simpa [old.property] using hjArray)).val <
      2^34 + (terms.val % 4) * AspisR1BatchedAllPrefix.cap := by
    have h := hrawAt old _hold j.val hj
    simpa using h
  obtain ⟨previous, hread, hprevious⟩ := WP.spec_imp_exists
    (Array.index_usize_spec old j (by simpa [old.property, h4] using hj))
  have hrawPrevious : previous.val <
      2^34 + (terms.val % 4) * AspisR1BatchedAllPrefix.cap := by
    simpa [hprevious] using hraw
  obtain ⟨product, updated, hproduct, hbody⟩ :=
    AspisR1BatchedWeightsPushBodyBoundedV5.push_body_step_bounded_of_reads
    index limbs iter self basis j iterNext old back previous terms hnext hj
    hlimbBound hbasis hvec hrawPrevious hread
  exact ⟨product, updated, back, hproduct, hbody⟩
#print axioms push_body_step_bounded_of_state
end AspisR1BatchedWeightsPushBodyBoundedV6
