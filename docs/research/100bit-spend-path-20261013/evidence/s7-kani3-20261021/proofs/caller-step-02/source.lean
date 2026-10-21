import S7Kani2OwnedPushModel
import S7Kani3PhaseInvariant
import S8Kani2CallerJoin
set_option autoImplicit false
noncomputable section
namespace S7Kani3CallerStep
open Aeneas Aeneas.Std Result
open S7Kani2AccumulatorLoop (BatchedWeights K)
open S7Kani2OwnedRowRefinement (makeRow powerLimb)
open S8OwnedP6ValueModel (rowAt Row)
open S8Kani2CallerJoin (CallerInvariant)
open AspisR1BatchedFoldSourceStep (sourcePush_mod product_bound)

theorem rowAt_makeRow (x : Fin 4 → U64) (k : Fin 4) :
    rowAt (makeRow x) k=x k := by fin_cases k <;> rfl

/-- Complete reached-state congruence preservation for one actual emitted
owned Vec push. Every other raw row is framed; the changed sum is an exact
Function.update rather than an independently chosen postcondition. -/
theorem push_caller_invariant
    (weights : BatchedWeights) (old : S8OwnedP6Finish.Weights)
    (sum : Nat → Fin 4 → Nat) (caller : CallerInvariant weights.raw old sum)
    (index : Usize) (power : K) (basis : U32) (x : Fin 4 → U64)
    (hindex : index.val<weights.raw.length)
    (hget : weights.raw.val[index.val]?=some (makeRow x))
    (hcanon : ∀ k, (powerLimb power k).val<2^31-1)
    (hbasis : basis.val<2^31-1)
    (hphase : ∀ k, S7Kani3PhaseInvariant.Phase weights.terms.val (x k).val) :
    ∃ y : Fin 4 → U64,
      S7Kani2OwnedPush.push_owned weights index power basis=
        ok {weights with raw := weights.raw.set index (makeRow y)} ∧
      CallerInvariant (weights.raw.set index (makeRow y)) old
        (Function.update sum index.val (fun k => sum index.val k+(powerLimb power k).val*basis.val)) ∧
      (∀ k, S7Kani3PhaseInvariant.Phase (weights.terms.val+1) (y k).val) := by
  obtain ⟨row,hread,hrow⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec weights.raw index hindex)
  have hi : index.val<weights.raw.val.length := hindex
  have hroweq : row=makeRow x := by
    have hh : weights.raw.val[index.val]?=some row := by
      rw [List.getElem?_eq_getElem hi]; exact congrArg some hrow.symm
    exact Option.some.inj (hh.symm.trans hget)
  have hread' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
      weights.raw index=ok (makeRow x) := by
    rw [alloc.vec.Vec.index_slice_index]; simpa only [hroweq] using hread
  obtain ⟨y,hy,hvalue⟩ := S7Kani2OwnedPushModel.push_refines_model weights index power basis x
    hindex hread' hcanon hbasis hphase
  refine ⟨y,hy,⟨?_,?_⟩,?_⟩
  · simpa using caller.lengths
  · intro j row hread k
    by_cases hj : j=index.val
    · subst j
      have he : row=makeRow y := by
        have hsame : (weights.raw.set index (makeRow y)).val[index.val]?=some (makeRow y) := by
          change (weights.raw.val.set index.val (makeRow y))[index.val]?=some (makeRow y)
          simp [List.getElem?_set,hi]
        exact Option.some.inj (hread.symm.trans hsame)
      subst row
      simp only [rowAt_makeRow,Function.update_self,hvalue]
      change AspisR1BatchedFoldSourceStep.sourcePush weights.terms.val (x k).val
        ((powerLimb power k).val*basis.val)%2147483647=
          (sum index.val k+(powerLimb power k).val*basis.val)%2147483647
      rw [sourcePush_mod,Nat.add_mod,Nat.add_mod]
      have hc := caller.congruence index.val (makeRow x) hget k
      simpa only [rowAt_makeRow] using congrArg
        (fun r => (r+((powerLimb power k).val*basis.val)%2147483647)%2147483647) hc
    · have hold : weights.raw.val[j]?=some row := by
        change (weights.raw.val.set index.val (makeRow y))[j]?=some row at hread
        simpa [List.getElem?_set,hj,Ne.symm hj] using hread
      simpa only [Function.update_of_ne hj] using caller.congruence j row hold k
  · intro k
    rw [hvalue k]
    exact (S7Kani3PhaseInvariant.push_phase weights.terms.val (x k).val
      ((powerLimb power k).val*basis.val) (hphase k) (product_bound (hcanon k) hbasis)).2

#print axioms rowAt_makeRow
#print axioms push_caller_invariant
end S7Kani3CallerStep
