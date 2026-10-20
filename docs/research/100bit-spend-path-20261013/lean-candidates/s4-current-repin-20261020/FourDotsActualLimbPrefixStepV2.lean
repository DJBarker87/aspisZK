import FourDotsActualLimbLocalArithmeticV1
import Aeneas.Std.Array.Array
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std

namespace AspisR1FastDotsActualLimbPrefixStepV2

abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := Std.U32
abbrev cap : Nat := (2147483646)^2

def cell (a : Array U64 8#usize) (j : Fin 8) : Nat :=
  (a.val[j.val]'(by simpa [a.property] using j.isLt)).val

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

/-- A write whose new value is already below `bound` preserves that
    pointwise bound; all other entries retain their prior value. -/
theorem set_preserves_pointwise_bound
    (a : Array U64 8#usize) (i : Usize) (x : U64) (bound : Nat)
    (hbase : ∀ j : Fin 8, cell a j ≤ bound)
    (hnew : x.val ≤ bound) :
    ∀ j : Fin 8, cell (a.set i x) j ≤ bound := by
  intro j
  have hjset : j.val < (a.val.set i.val x).length := by
    simpa [a.property] using j.isLt
  change ((a.val.set i.val x)[j.val]'hjset).val ≤ bound
  by_cases heq : i.val = j.val
  · have hself : (a.val.set i.val x)[j.val]'hjset = x := by
      have hs := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hjset)
      simpa [heq] using hs
    rw [hself]
    exact hnew
  · have hother : (a.val.set i.val x)[j.val]'hjset =
        a.val[j.val]'(by simpa [a.property] using j.isLt) := by
      exact List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val) heq hjset
    rw [hother]
    exact hbase j

/-- The actual generated inner-limb body advances the array from a uniform
    `3 * cap` bound to `4 * cap` in one successful step, using its emitted
    multiply/add/update sequence. -/
theorem inner_body_success_advances_bound
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coefficient : Array U32 8#usize) (iter iter' : AspisR1FastDotsActualLimbLocalArithmeticV1.Range)
    (sums sums' : Array U64 8#usize) (scalar scalar' : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hcoeff : ∀ i : Fin 8,
      (coefficient.val[i.val]'(by simpa [coefficient.property] using i.isLt)).val < 2147483647)
    (hbase4 : ∀ i : Fin 8, cell sums i ≤ 4 * cap)
    (hcurrent : ∀ i : Fin 8, i.val = iter.start.val → cell sums i ≤ 3 * cap)
    (hscalar : scalar.val < 2147483647)
    (hbody : AspisR1FastDotsActualLimbLocalArithmeticV1.InnerBody
      ops coefficient iter sums scalar = .ok (.cont (iter', (sums', scalar')))):
    iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧
      ∀ j : Fin 8, cell sums' j ≤ 4 * cap := by
  obtain ⟨limb, coeff, oldSum, product, newSum,
      hcoeffRead, hsumRead, hmul, hadd, hproductValue, hproductBound,
      hnewValue, updated, hupdate, hresult, hlimbEq, hOldBound,
      hiterStart, hiterEnd⟩ :=
    AspisR1FastDotsActualLimbLocalArithmeticV1.inner_body_success_arithmetic_at_current
      ops coefficient iter iter' sums sums' scalar scalar' hcoeff hcurrent hscalar hbody
  have hnew4 : newSum.val ≤ 4 * cap := by
    rw [hnewValue]
    calc
      oldSum.val + product.val ≤ 3 * cap + cap := Nat.add_le_add hOldBound hproductBound
      _ = 4 * cap := by ring
  have hIndex : limb.val < 8 := by
    have hi := index_success_bound sums limb oldSum hsumRead
    simpa [sums.property] using hi
  have hupdateSet : Array.update sums limb newSum = .ok (sums.set limb newSum) := by
    obtain ⟨out, hrun, hset⟩ := WP.spec_imp_exists
      (Array.update_spec sums limb newSum (by simpa [sums.property] using hIndex))
    simpa only [hset] using hrun
  have hupdated : updated = sums.set limb newSum :=
    Result.ok.inj (hupdate.symm.trans hupdateSet)
  have hupdatedBound := set_preserves_pointwise_bound sums limb newSum (4 * cap) hbase4 hnew4
  refine ⟨hiterStart, hiterEnd, ?_⟩
  intro j
  have hfinal : sums' = sums.set limb newSum := hresult.trans hupdated
  rw [hfinal]
  exact hupdatedBound j

#print axioms set_preserves_pointwise_bound
#print axioms inner_body_success_advances_bound

end AspisR1FastDotsActualLimbPrefixStepV2
