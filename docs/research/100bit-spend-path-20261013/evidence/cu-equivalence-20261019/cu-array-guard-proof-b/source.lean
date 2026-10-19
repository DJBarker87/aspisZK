import AspisR1CuArraySource.Push

/-! Exact execution of the selected emitted Guard.push_unchecked declaration
under its explicit safe-domain primitive interpretation. All bounds needed by
the unsafe operations are discharged. Primitive/frontend admission and the
enclosing standard-library loop remain separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsArrayGuard
open Aeneas Aeneas.Std Result
abbrev Guard := AspisR1CuArraySource.core.array.Guard

theorem increment_success {T : Type} (buffer : Slice T) (index : Usize)
    (h : index.val < buffer.length) :
    ∃ next : Usize, UScalar.add index 1#usize = .ok next ∧
      next.val = index.val+1 := by
  have hone : (1#usize).val = 1 := by scalar_tac
  have hmax : index.val + (1#usize).val ≤ UScalar.max .Usize := by
    have hb := Slice.length_ineq buffer
    rw [hone,UScalar.max_USize_eq]
    omega
  have hs := UScalar.add_spec (x:=index) (y:=1#usize) hmax
  cases he : UScalar.add index 1#usize with
  | ok next =>
    refine ⟨next,rfl,?_⟩
    simpa only [show (index + 1#usize : Result Usize) = UScalar.add index 1#usize by rfl,
      he,WP.spec,WP.theta,WP.wp_return,hone] using hs
  | fail e =>
    have hf : False := by
      simpa only [show (index + 1#usize : Result Usize) = UScalar.add index 1#usize by rfl,
        he,WP.spec,WP.theta] using hs
    exact hf.elim
  | div =>
    have hf : False := by
      simpa only [show (index + 1#usize : Result Usize) = UScalar.add index 1#usize by rfl,
        he,WP.spec,WP.theta] using hs
    exact hf.elim

theorem index_success {T : Type} (buffer : Slice T) (index : Usize)
    (h : index.val < buffer.length) :
    Slice.index_mut_usize buffer index =
      .ok (buffer.val[index.val]'h, Slice.set buffer index) := by
  simp only [Slice.index_mut_usize,Slice.index_usize,Slice.getElem?_Usize_eq,
    List.getElem?_eq_getElem h,bind_tc_ok]

theorem source_success {T : Type} (self : Guard T) (item : T)
    (h : self.initialized.val < self.array_mut.length) :
    ∃ next : Usize, next.val = self.initialized.val+1 ∧
      AspisR1CuArraySource.core.array.Guard.push_unchecked self item =
        .ok (({array_mut:=self.array_mut.set self.initialized (some item),initialized:=next} : Guard T),
          fun replacement : Guard T => {self with array_mut:=replacement.array_mut}) := by
  obtain ⟨next,hn,hnv⟩ := increment_success self.array_mut self.initialized h
  refine ⟨next,hnv,?_⟩
  simp only [AspisR1CuArraySource.core.array.Guard.push_unchecked,
    AspisR1CuArraySource.core.slice.Slice.get_unchecked_mut,
    core.slice.index.SliceIndexUsizeSlice,core.slice.index.Usize.index_mut,
    index_success self.array_mut self.initialized h,bind_tc_ok,
    AspisR1CuArraySource.core.mem.maybe_uninit.MaybeUninit.write,
    AspisR1CuArraySource.core.num.Usize.unchecked_add,hn]
  rfl

theorem frame {T : Type} (self : Guard T) (item : T) (j : Nat)
    (hne : j ≠ self.initialized.val) :
    (self.array_mut.set self.initialized (some item)).val[j]? =
      self.array_mut.val[j]? := by
  simp only [Slice.set,Slice.setAtNat]
  exact List.getElem?_set_ne (by omega)

theorem written {T : Type} (self : Guard T) (item : T)
    (h : self.initialized.val < self.array_mut.length) :
    (self.array_mut.set self.initialized (some item)).val[self.initialized.val]? =
      some (some item) := by
  simp only [Slice.set,Slice.setAtNat]
  exact List.getElem?_set_self h

#print axioms increment_success
#print axioms index_success
#print axioms source_success
#print axioms frame
#print axioms written
end AspisR1.CuSavingsArrayGuard
