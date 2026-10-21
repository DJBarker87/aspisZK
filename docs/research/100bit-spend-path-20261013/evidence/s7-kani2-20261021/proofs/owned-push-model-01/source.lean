import S7Kani2OwnedPush
import S7Kani2OwnedRowRefinement
import Init.Data.Nat.Bitwise.Lemmas

/-! Actual extracted Vec step, including the flush test, refined to the
existing sourcePush model for every bounded index and arbitrary row words. -/
set_option autoImplicit false
namespace S7Kani2OwnedPushModel
open Aeneas Aeneas.Std Result
open S7Kani2AccumulatorLoop (BatchedWeights K)
open S7Kani2OwnedRow (Row residue_owned)
open S7Kani2OwnedRowRefinement (makeRow powerLimb)

theorem phase_flag (terms : Usize) :
    (terms &&& 3#usize = 3#usize) ↔ terms.val%4=3 := by
  have hv : (UScalar.and terms (3#usize)).val=terms.val%4 := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod terms.val 2
  constructor
  · intro h
    have he := congrArg UScalar.val h
    simpa only [hv] using he
  · intro h
    apply UScalar.eq_of_val_eq
    simpa only [hv] using h

theorem push_of_row (weights : BatchedWeights) (index : Usize) (power : K) (basis : U32)
    (row updated : Row) (hindex : index.val<weights.raw.length)
    (hread : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row) weights.raw index=ok row)
    (hrow : residue_owned row power basis ((weights.terms &&& 3#usize)=3#usize)=ok updated) :
    S7Kani2OwnedPush.push_owned weights index power basis =
      ok {weights with raw := weights.raw.set index updated} := by
  obtain ⟨⟨old,back⟩,hmut,_,hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec weights.raw index hindex)
  have hm : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Row)
      weights.raw index = ok (old,back) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hmut
  simp only [S7Kani2OwnedPush.push_owned,hread,lift,bind_tc_ok,hrow,hm,hback]
  rfl

/-- No step-equality or arithmetic-callee premise: source Vec read, flush,
four checked scalar transitions and exact setter are all connected. The
canonicality/phase invariant is the explicit caller domain. -/
theorem push_refines_model (weights : BatchedWeights) (index : Usize) (power : K)
    (basis : U32) (x : Fin 4 → U64) (hindex : index.val<weights.raw.length)
    (hread : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
      weights.raw index=ok (makeRow x))
    (hcanon : ∀ j, (powerLimb power j).val<2^31-1) (hbasis : basis.val<2^31-1)
    (hphase : ∀ j, (x j).val<2^34+(weights.terms.val%4)*(2^31-2)^2) :
    ∃ y : Fin 4 → U64,
      S7Kani2OwnedPush.push_owned weights index power basis =
        ok {weights with raw := weights.raw.set index (makeRow y)} ∧
      ∀ j, (y j).val = AspisR1BatchedFoldSourceStep.sourcePush weights.terms.val (x j).val
        ((powerLimb power j).val*basis.val) := by
  obtain ⟨y,hy,hvalue⟩ := S7Kani2OwnedRowRefinement.literal_row_refines_model
    x power basis weights.terms.val hcanon hbasis hphase
  have hflag : residue_owned (makeRow x) power basis
      ((weights.terms &&& 3#usize)=3#usize)=ok (makeRow y) := by
    simpa only [phase_flag] using hy
  exact ⟨y,push_of_row weights index power basis _ _ hindex hread hflag,hvalue⟩

#print axioms phase_flag
#print axioms push_of_row
#print axioms push_refines_model
end S7Kani2OwnedPushModel
