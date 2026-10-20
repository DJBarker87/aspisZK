import FourDotsActualLimbPrefixStepV2
import Aeneas.Std.Array.Array
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualLimbPrefixStepV3

abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := Std.U32
abbrev Range := AspisR1FastDotsActualLimbLocalArithmeticV1.Range
abbrev cap : Nat := (2147483646)^2

def cell (a : Array U64 8#usize) (j : Fin 8) : Nat :=
  (a.val[j.val]'(by simpa [a.property] using j.isLt)).val

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem index_success_bound {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) : i.val < n.val := by
  have hlen : i.val < a.val.length := by
    by_contra hnot
    have hnone : a[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [a.property] using hlen

private theorem body_success_starts_before_end
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coefficient : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize)
    (scalar scalar' : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hbody : AspisR1FastDotsActualLimbLocalArithmeticV1.InnerBody
      ops coefficient iter sums scalar = .ok (.cont (iter', sums', scalar'))) :
    iter.start.val < iter.end.val := by
  unfold AspisR1FastDotsActualLimbLocalArithmeticV1.InnerBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      cases Result.ok.inj hrest
  | some limb =>
      have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize)
        (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter
      rw [hnext, WP.spec_ok] at hspec
      by_cases hlt : iter.start.val < iter.end.val
      · exact hlt
      · simp only [hlt, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨hnone, _⟩, _⟩
        cases hnone

/-- One actual successful inner-body step preserves the processed-prefix
    envelope and the untouched suffix envelope. Earlier limbs may already be
    at 4cap; this step only requires the current and later limbs to remain at
    3cap before they are visited. -/
theorem inner_body_success_preserves_prefix
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coefficient : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize)
    (scalar scalar' : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hcoeff : ∀ i : Fin 8,
      (coefficient.val[i.val]'(by simpa [coefficient.property] using i.isLt)).val < 2147483647)
    (hbase4 : ∀ i : Fin 8, cell sums i ≤ 4 * cap)
    (hsuffix : ∀ i : Fin 8, iter.start.val ≤ i.val → cell sums i ≤ 3 * cap)
    (hscalar : scalar.val < 2147483647)
    (hbody : AspisR1FastDotsActualLimbLocalArithmeticV1.InnerBody
      ops coefficient iter sums scalar = .ok (.cont (iter', sums', scalar'))) :
    iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧
      (∀ i : Fin 8, iter'.start.val ≤ i.val → cell sums' i ≤ 3 * cap) ∧
      (∀ i : Fin 8, cell sums' i ≤ 4 * cap) := by
  have hlt := body_success_starts_before_end ops coefficient iter iter' sums sums' scalar scalar' hbody
  have hcurrent : ∀ i : Fin 8, i.val = iter.start.val → cell sums i ≤ 3 * cap := by
    intro i hi
    exact hsuffix i (by omega)
  obtain ⟨hiterStart, hiterEnd, hglobal⟩ :=
    AspisR1FastDotsActualLimbPrefixStepV2.inner_body_success_advances_bound
      ops coefficient iter iter' sums sums' scalar scalar' hcoeff hbase4
      hcurrent hscalar hbody
  obtain ⟨limb, coeff, oldSum, product, newSum,
      hcoeffRead, hsumRead, hmul, hadd, hproductValue, hproductBound,
      hnewValue, updated, hupdate, hresult, hlimbEq, hOldBound,
      _hiterStart, _hiterEnd⟩ :=
    AspisR1FastDotsActualLimbLocalArithmeticV1.inner_body_success_arithmetic_at_current
      ops coefficient iter iter' sums sums' scalar scalar' hcoeff hcurrent hscalar hbody
  have hIndex : limb.val < 8 := by
    have hi := index_success_bound sums limb oldSum hsumRead
    simpa [sums.property] using hi
  have hupdateSet : Array.update sums limb newSum = .ok (sums.set limb newSum) := by
    obtain ⟨out, hrun, hset⟩ := WP.spec_imp_exists
      (Array.update_spec sums limb newSum (by simpa [sums.property] using hIndex))
    simpa only [hset] using hrun
  have hupdated : updated = sums.set limb newSum :=
    Result.ok.inj (hupdate.symm.trans hupdateSet)
  have hfinal : sums' = sums.set limb newSum := hresult.trans hupdated
  refine ⟨hiterStart, hiterEnd, ?_, hglobal⟩
  intro i hi
  have hafter : iter.start.val < i.val := by rw [hiterStart] at hi; omega
  have hne : limb.val ≠ i.val := by rw [hlimbEq]; omega
  have hiSet : i.val < (sums.val.set limb.val newSum).length := by
    simpa [sums.property] using i.isLt
  have hiOrig : i.val < sums.val.length := by
    simpa [sums.property] using i.isLt
  have hsameCell : cell sums' i = cell sums i := by
    unfold cell
    rw [hfinal]
    change ((sums.val.set limb.val newSum)[i.val]'hiSet).val =
      (sums.val[i.val]'hiOrig).val
    rw [List.getElem_set_ne (l := sums.val) (i := limb.val) (j := i.val) hne hiSet]
  rw [hsameCell]
  exact hsuffix i (by omega)

#print axioms inner_body_success_preserves_prefix

end AspisR1FastDotsActualLimbPrefixStepV3
