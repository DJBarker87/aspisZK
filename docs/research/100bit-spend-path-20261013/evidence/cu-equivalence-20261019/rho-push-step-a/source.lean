import CuSavingsRhoValue

/-! One actual emitted update-loop iteration, including both levels of array
access and the mutable Vec handback. The range iterator and enclosing loop
invariant are intentionally separate obligations. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoPushStep
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1CuRho
open AspisR1.CuSavingsRhoValue
open AspisR1.CuSavingsResidues
open AspisV8R17.RawReducer
abbrev Raw4 := Array U64 4#usize
abbrev Limbs := Array U32 4#usize
abbrev Range := Aeneas.Std.core.ops.range.Range Usize

theorem vec_read {T : Type} (v : alloc.vec.Vec T) (i : Usize)
    (hi : i.val < v.val.length) :
    alloc.vec.Vec.index (Aeneas.Std.core.slice.index.SliceIndexUsizeSlice T) v i =
      .ok (v.val[i.val]'hi) := by
  unfold alloc.vec.Vec.index Aeneas.Std.core.slice.index.SliceIndexUsizeSlice
  change Slice.index_usize v i = _
  unfold Slice.index_usize
  simp only [Slice.getElem?_Usize_eq,List.getElem?_eq_getElem hi]
  rfl

theorem vec_read_mut {T : Type} (v : alloc.vec.Vec T) (i : Usize)
    (hi : i.val < v.val.length) :
    alloc.vec.Vec.index_mut (Aeneas.Std.core.slice.index.SliceIndexUsizeSlice T) v i =
      .ok (v.val[i.val]'hi,Slice.set v i) := by
  unfold alloc.vec.Vec.index_mut Aeneas.Std.core.slice.index.SliceIndexUsizeSlice
  change Slice.index_mut_usize v i = _
  unfold Slice.index_mut_usize Slice.index_usize
  simp only [Slice.getElem?_Usize_eq,List.getElem?_eq_getElem hi,bind_tc_ok]

theorem array_update {T : Type} (a : Array T 4#usize) (j : Usize)
    (hj : j.val < 4) (value : T) : Array.update a j value = .ok (a.set j value) := by
  obtain ⟨out,hr,heq⟩ := WP.spec_imp_exists (Array.update_spec a j value
    (by simpa [a.property] using hj))
  simpa only [heq] using hr

theorem source_update_step (self : verifier.BatchedWeights) (index : Usize)
    (basis : field.M31) (limbs : Limbs) (iter next : Range) (j : Usize)
    (hnext : Aeneas.Std.core.iter.range.IteratorRange.next
      Aeneas.Std.core.iter.range.StepUsize iter = .ok (some j,next))
    (hi : index.val < self.raw.val.length) (hj : j.val < 4)
    (hr : RhoBound (wordAt (self.raw.val[index.val]'hi) ⟨j.val,hj⟩).val self.terms.val)
    (hp : (wordAt limbs ⟨j.val,hj⟩).val < P) (hb : basis.val < P) :
    ∃ value : U64,
      verifier.BatchedWeights.push_loop0.body index limbs iter self basis =
        .ok (.cont (next,
          { self with raw := Slice.set self.raw index
            ((self.raw.val[index.val]'hi).set j value) },basis)) ∧
      value.val = (wordAt (self.raw.val[index.val]'hi) ⟨j.val,hj⟩).val +
        (wordAt limbs ⟨j.val,hj⟩).val*basis.val := by
  let raw := self.raw.val[index.val]'hi
  let power := wordAt limbs ⟨j.val,hj⟩
  let old := wordAt raw ⟨j.val,hj⟩
  have hpower := AspisR1.ExtractedCurrentReducer.cast_widen_value power
  have hbasis := AspisR1.ExtractedCurrentReducer.cast_widen_value basis
  have hprod := canonical_product_bound power.val basis.val hp hb
  have hfit := rho_add_fits old.val self.terms.val (power.val*basis.val) hr hprod
  obtain ⟨product,hm,hv⟩ := AspisR1.ExtractedCurrentReducerOps.mul_success
    (UScalar.cast .U64 power) (UScalar.cast .U64 basis) (by
      rw [hpower,hbasis];omega)
  rw [hpower,hbasis] at hv
  obtain ⟨value,ha,hvalue⟩ := AspisR1.ExtractedCurrentReducerOps.add_success old product
    (by rw [hv];exact hfit)
  refine ⟨value,?_,by simpa only [hv] using hvalue⟩
  simp only [verifier.BatchedWeights.push_loop0.body,hnext,bind_tc_ok,
    array_read limbs j hj,vec_read_mut self.raw index hi,array_read raw j hj,
    core.convert.num.FromU64U32.from,lift,hm,ha,array_update raw j hj value]

#print axioms vec_read
#print axioms vec_read_mut
#print axioms array_update
#print axioms source_update_step
end AspisR1.CuSavingsRhoPushStep
