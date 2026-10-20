import FourDotsActualLimbLocalArithmeticV1
import FourDotsActualInnerLoopLinearBoundV1

open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace AspisR1FastDotsActualLimbExactStepRootV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U64 := Std.U64
abbrev U32 := Std.U32
abbrev Range := core.ops.range.Range Usize
abbrev M31 := AspisR1FastDotsCurrent.aspis_core.field.M31
abbrev InnerBody := AspisR1FastDotsActualLimbLocalArithmeticV1.InnerBody
abbrev cap := AspisR1FastDotsActualLimbLocalArithmeticV1.cap
abbrev cell := AspisR1FastDotsActualInnerLoopLinearBoundV1.cell

def coeffCell (a : Array U32 8#usize) (j : Fin 8) : Nat :=
  (a.val[j.val]'(by simpa [a.property] using j.isLt)).val

private theorem index_value {T : Type} {N : Usize}
    (a : Array T N) (i : Usize) (x : T)
    (h : Array.index_usize a i = .ok x) :
    ∃ hi : i.val < a.val.length, x = a.val[i.val]'hi := by
  have hi : i.val < a.val.length := by
    by_contra hn
    have he : a[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hn)
    unfold Array.index_usize at h
    rw [he] at h
    cases h
  obtain ⟨y,hy,hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hi)
  exact ⟨hi,(Result.ok.inj (h.symm.trans hy)).trans hvalue⟩

/-- The exact natural-value update of the actual emitted limb body. Only the
visited coordinate changes; the same actual coefficient/scalar product is
added once. This strengthens the previous range-only contract. -/
theorem actual_limb_body_success_exact_step
    (ops : Ops) (coefficient : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize) (scalar scalar' : M31)
    (hcoeff : ∀ j : Fin 8, coeffCell coefficient j < 2147483647)
    (hcurrent : ∀ j : Fin 8, j.val = iter.start.val → cell sums j ≤ 3 * cap)
    (hscalar : scalar.val < 2147483647)
    (hbody : InnerBody ops coefficient iter sums scalar =
      .ok (.cont (iter',sums',scalar'))) :
    iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧
    ∀ j : Fin 8, cell sums' j =
      if j.val = iter.start.val then cell sums j + coeffCell coefficient j * scalar.val
      else cell sums j := by
  obtain ⟨limb,coeff,oldSum,product,newSum,hcoeffRead,hsumRead,_hmul,_hadd,
      hproduct,_hproductBound,hnew,updated,hupdate,hresult,hlimb,_hold,hstart,hend⟩ :=
    AspisR1FastDotsActualLimbLocalArithmeticV1.inner_body_success_arithmetic_at_current
      ops coefficient iter iter' sums sums' scalar scalar' hcoeff hcurrent hscalar hbody
  obtain ⟨hindex,holdValue⟩ := index_value sums limb oldSum hsumRead
  obtain ⟨hcoeffIndex,hcoeffValue⟩ := index_value coefficient limb coeff hcoeffRead
  obtain ⟨out,hrun,hset⟩ := WP.spec_imp_exists
    (Array.update_spec sums limb newSum hindex)
  have hfinal : sums' = sums.set limb newSum :=
    hresult.trans ((Result.ok.inj (hupdate.symm.trans hrun)).trans hset)
  refine ⟨hstart,hend,?_⟩
  intro j
  have hj : j.val < sums.val.length := by simpa [sums.property] using j.isLt
  have hjset : j.val < (sums.val.set limb.val newSum).length := by simpa using hj
  by_cases heq : j.val = iter.start.val
  · have hlimbJ : limb.val = j.val := by rw [hlimb,heq]
    have hcell : cell sums' j = newSum.val := by
      unfold cell AspisR1FastDotsActualInnerLoopLinearBoundV1.cell
      rw [hfinal]
      change ((sums.val.set limb.val newSum)[j.val]'hjset).val = newSum.val
      have hself := List.getElem_set_self (l := sums.val) (i := limb.val)
        (a := newSum) (by simpa using hindex)
      simpa only [hlimbJ] using congrArg UScalar.val hself
    have hold : oldSum.val = cell sums j := by
      rw [holdValue]
      simp only [cell,AspisR1FastDotsActualInnerLoopLinearBoundV1.cell,hlimbJ]
    have hco : coeff.val = coeffCell coefficient j := by
      rw [hcoeffValue]
      simp only [coeffCell,hlimbJ]
    rw [if_pos heq,hcell,hnew,hproduct,hold,hco]
  · have hne : limb.val ≠ j.val := by rw [hlimb]; omega
    rw [if_neg heq]
    unfold cell AspisR1FastDotsActualInnerLoopLinearBoundV1.cell
    rw [hfinal]
    change ((sums.val.set limb.val newSum)[j.val]'hjset).val = _
    rw [List.getElem_set_ne (l := sums.val) (i := limb.val) (j := j.val) hne hjset]

#print axioms actual_limb_body_success_exact_step
end AspisR1FastDotsActualLimbExactStepRootV1
