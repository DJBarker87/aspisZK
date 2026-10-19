import AspisR1BatchedWeightsPushBodyValueStepV1
import AspisR1BatchedWeightsPushBodyBoundedV6
import ExtractedCurrentCM31Mul
import ExtractedCurrentReducerOps
import AspisR1BatchedAllPrefix
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1BatchedWeightsPushBodyValueStepV3
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

private theorem four_limb_selected_canonical
    (a b c d : aspis_core.field.M31)
    (ha : a.val < AspisV8R17.RawReducer.P)
    (hb : b.val < AspisV8R17.RawReducer.P)
    (hc : c.val < AspisV8R17.RawReducer.P)
    (hd : d.val < AspisV8R17.RawReducer.P)
    (j : Usize) (hj : j.val < 4) :
    ((Array.make 4#usize [a,b,c,d]).val[j.val]'
      (by change j.val < 4; exact hj)).val < AspisV8R17.RawReducer.P := by
  have hcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases hcases with h | h | h | h
  · simpa [Array.make, h] using ha
  · simpa [Array.make, h] using hb
  · simpa [Array.make, h] using hc
  · simpa [Array.make, h] using hd

/-- Fully source-shaped bounded body step for `push`: derives array/vector
read success from indices and exposes the selected arithmetic update, while
retaining the cadence invariant as the only raw-state bound. -/
theorem push_body_step_power_value
    (index : Usize) (iter : Range) (self : BW)
    (power : aspis_core.field.QM31) (basis : aspis_core.field.M31)
    (j : Usize) (iterNext : Range) (terms : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some j, iterNext))
    (hj : j.val < 4)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hindex : index.val < self.raw.length)
    (hrawSelected : ∀ (old : Array Std.U64 4#usize),
      old = self.raw.val[index.val]'(by simpa using hindex) →
      (old.val[j.val]'(by simpa [old.property] using hj)).val <
          2^34 + (terms.val % 4) * AspisR1BatchedAllPrefix.cap) :
    ∃ product sum : Std.U64, ∃ updated : Array Std.U64 4#usize,
    ∃ old : Array Std.U64 4#usize, ∃ back : Array Std.U64 4#usize → Raw,
      product.val =
        ((Array.make 4#usize [power.c0.a, power.c0.b, power.c1.a, power.c1.b]).val[j.val]'
          (by change j.val < 4; exact hj)).val * basis.val ∧
      sum.val = (old.val[j.val]'(by simpa [old.property] using hj)).val + product.val ∧
      old = self.raw.val[index.val]'(by simpa using hindex) ∧
      back = self.raw.set index ∧
      updated = old.set j sum ∧
      batched_weights.BatchedWeights.push_loop.body index
        (Array.make 4#usize [power.c0.a, power.c0.b, power.c1.a, power.c1.b])
        iter self basis = .ok (.cont (iterNext, { self with raw := back updated }, basis)) := by
  have h4 : (4#usize).val = 4 := by decide
  have hjArray : j.val < (4#usize).val := by simpa [h4] using hj
  have hlimbBound := four_limb_selected_canonical
    power.c0.a power.c0.b power.c1.a power.c1.b ha hb hc hd j hj
  let limbs := Array.make 4#usize [power.c0.a, power.c0.b, power.c1.a, power.c1.b]
  let limb := limbs.val[j.val]'(by change j.val < 4; exact hj)
  have hlimbRead : Array.index_usize limbs j = .ok limb :=
    index_usize_ok limbs j (by change j.val < 4; exact hj)
  have hlimbBound : limb.val < AspisV8R17.RawReducer.P := by simpa [limbs, limb] using hlimbBound
  obtain ⟨⟨old, back⟩, hmut, hold, hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec self.raw index hindex)
  have hvec : alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize))
      self.raw index = .ok (old, back) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hmut
  have hrawOld : (old.val[j.val]'(by simpa [old.property] using hjArray)).val <
      2^34 + (terms.val % 4) * AspisR1BatchedAllPrefix.cap := by
    exact hrawSelected old hold
  obtain ⟨previous, hread, hprev⟩ := WP.spec_imp_exists
    (Array.index_usize_spec old j (by simpa [old.property, h4] using hj))
  have hrawPrevious : previous.val <
      2^34 + (terms.val % 4) * AspisR1BatchedAllPrefix.cap := by
    simpa [hprev] using hrawOld
  obtain ⟨product, sum, updated, hproduct, hsum, hset, hbody⟩ :=
    AspisR1BatchedWeightsPushBodyValueStepV1.push_body_step_value
      index limbs iter self basis j iterNext limb old back previous terms
      hnext hj hlimbRead hlimbBound hbasis hvec hrawPrevious hread
  refine ⟨product, sum, updated, old, back, ?_, ?_, hold, hback, hset, hbody⟩
  · simpa [limbs, limb] using hproduct.symm
  · simpa [hprev] using hsum
#print axioms push_body_step_power_value
end AspisR1BatchedWeightsPushBodyValueStepV3
