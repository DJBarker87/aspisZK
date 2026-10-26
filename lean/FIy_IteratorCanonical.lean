import FIy_IteratorTraversal
import FIx_ArithmeticTotal
set_option autoImplicit false
namespace AspisR1.FIy_IteratorCanonical
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIy_IteratorTraversal
/-- With a canonical selector and canonical cells in the visited suffix,
the actual generated loop derives every multiply result, output canonicality,
and decoded value, together with finite termination/writeback semantics. -/
theorem loop3_finite_of_canonical_cells
    (iter : IterMut) (back : IterMut → IterMut) (rangeSelector : QM)
    (n : Nat)
    (hlen : iter.slice.len = iter.i + n)
    (hselector : Canon rangeSelector)
    (hcells : ∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
      Canon (iter.slice.val[j])) :
    ∃ values : Nat → QM,
      (∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
        Canon (values j) ∧
        decode (values j) = decode rangeSelector * decode (iter.slice.val[j])) ∧
      ∃ finalIter finalBack,
        Loop3 iter back rangeSelector = .ok (finalIter, finalBack) ∧
        finalIter.slice = iter.slice ∧
        finalIter.i = iter.i + n ∧
        ∀ im, finalBack im = back (deferredWrites values iter.i n im) := by
  classical
  have hlenVal : iter.slice.val.length = iter.i + n := by
    change iter.slice.val.length = iter.i + n at hlen
    exact hlen
  let values : Nat → QM := fun j =>
    if hj : iter.i ≤ j ∧ j < iter.slice.val.length then
      Classical.choose
        (FIx_ArithmeticTotal.mul rangeSelector (iter.slice.val[j]'hj.2
          ) hselector (hcells j hj.2 hj.1))
    else field.QM31.ZERO
  have hvalue : ∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
      Canon (values j) ∧
      decode (values j) = decode rangeSelector * decode (iter.slice.val[j]) := by
    intro j hj hjlo
    have hspec := Classical.choose_spec
      (FIx_ArithmeticTotal.mul rangeSelector (iter.slice.val[j]'hj
        ) hselector (hcells j hj hjlo))
    have hv : values j = Classical.choose
        (FIx_ArithmeticTotal.mul rangeSelector (iter.slice.val[j]'hj
          ) hselector (hcells j hj hjlo)) := by
      simp [values, hjlo, hj]
    rw [hv]
    exact ⟨hspec.2.1, hspec.2.2⟩
  have hproducts : ∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
      field.QM31.mul rangeSelector (iter.slice.val[j]) = .ok (values j) := by
    intro j hj hjlo
    have hspec := Classical.choose_spec
      (FIx_ArithmeticTotal.mul rangeSelector (iter.slice.val[j]'hj
        ) hselector (hcells j hj hjlo))
    have hv : values j = Classical.choose
        (FIx_ArithmeticTotal.mul rangeSelector (iter.slice.val[j]'hj
          ) hselector (hcells j hj hjlo)) := by
      simp [values, hjlo, hj]
    rw [hv]
    exact hspec.1
  obtain ⟨finalIter, finalBack, hrun, hslice, hindex, hback⟩ :=
    FIy_IteratorTraversal.products iter back rangeSelector values n hlen hproducts
  exact ⟨values, hvalue, finalIter, finalBack, hrun, hslice, hindex, hback⟩

/-- The concrete width used by `add_value_lanes`: starting at the beginning
of a 33-cell slice, all 33 multiplications and writebacks are derived from
the canonical selector and canonical input cells. -/
theorem add_value_lanes_loop3_33
    (iter : IterMut) (back : IterMut → IterMut) (rangeSelector : QM)
    (hstart : iter.i = 0) (hlen : iter.slice.len = (33 : Nat))
    (hselector : Canon rangeSelector)
    (hcells : ∀ j (hj : j < iter.slice.val.length), j < 33 →
      Canon (iter.slice.val[j])) :
    ∃ values : Nat → QM,
      (∀ j (hj : j < 33),
        Canon (values j) ∧
        decode (values j) = decode rangeSelector *
          decode (iter.slice.val[j]'(by rw [show iter.slice.val.length = iter.slice.len by rfl, hlen]; exact hj))) ∧
      ∃ finalIter finalBack,
        Loop3 iter back rangeSelector = .ok (finalIter, finalBack) ∧
        finalIter.slice = iter.slice ∧
        finalIter.i = (33 : Nat) ∧
        ∀ im, finalBack im = back (deferredWrites values 0 33 im) := by
  have hlen' : iter.slice.len = iter.i + 33 := by rw [hstart]; simp [hlen]
  have hcells' : ∀ j (hj : j < iter.slice.val.length), iter.i ≤ j →
      Canon (iter.slice.val[j]) := by
    intro j hj hlo
    apply hcells j hj
    rw [show iter.slice.val.length = iter.slice.len by rfl, hlen] at hj
    exact hj
  obtain ⟨values, hvalues, finalIter, finalBack, hrun, hslice, hindex, hback⟩ :=
    loop3_finite_of_canonical_cells iter back rangeSelector 33 hlen' hselector hcells'
  refine ⟨values, ?_, finalIter, finalBack, hrun, hslice, ?_, ?_⟩
  · intro j hj
    have hjval : j < iter.slice.val.length := by
      rw [show iter.slice.val.length = iter.slice.len by rfl, hlen]
      exact hj
    exact hvalues j hjval (by rw [hstart]; omega)
  · rw [hindex, hstart]
  · intro im
    rw [hback, hstart]


#print axioms loop3_finite_of_canonical_cells
#print axioms add_value_lanes_loop3_33
end AspisR1.FIy_IteratorCanonical
