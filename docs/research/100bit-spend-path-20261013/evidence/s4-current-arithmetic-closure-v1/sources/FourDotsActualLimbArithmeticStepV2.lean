import AspisR1FastDotsCurrent.FunsOpsV4
import Aeneas.Std.RangeIter
import ExtractedCurrentReducerOps
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualLimbArithmeticStepV2
abbrev InnerBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0.body
abbrev Range := core.ops.range.Range Usize
abbrev M31 := AspisR1FastDotsCurrent.aspis_core.field.M31
abbrev cap : Nat := (2147483646)^2

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem widen_u32_value (x : U32) :
    (core.convert.num.FromU64U32.from x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  apply BitVec.toNat_setWidth_of_le
  decide

private theorem index_success_bound {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) : i.val < n.val := by
  have hlen : i.val < a.val.length := by
    by_contra hnot
    have hnone : a[i]? = none :=
      List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [a.property] using hlen

/-- A successful emitted limb body performs the actual widened product and sum
    with their natural-number values. Canonical operands and the already
    accumulated batch-prefix bound make the checked U64 operations total. -/
theorem inner_body_success_arithmetic_update
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coefficient : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize) (scalar scalar' : M31)
    (hcoeff : ∀ i : Fin 8, (coefficient.val[i.val]'(by simpa [coefficient.property] using i.isLt)).val < 2147483647)
    (hprefix : ∀ i : Fin 8, (sums.val[i.val]'(by simpa [sums.property] using i.isLt)).val ≤ 3 * cap)
    (hscalar : scalar.val < 2147483647)
    (hbody : InnerBody ops coefficient iter sums scalar = .ok (.cont (iter', sums', scalar'))) :
    ∃ limb : Usize, ∃ coeff : U32, ∃ oldSum : U64,
      ∃ product : U64, ∃ newSum : U64,
        Array.index_usize coefficient limb = .ok coeff ∧
        Array.index_usize sums limb = .ok oldSum ∧
        UScalar.mul (core.convert.num.FromU64U32.from coeff)
          (core.convert.num.FromU64U32.from scalar) = .ok product ∧
        UScalar.add oldSum product = .ok newSum ∧
        product.val = coeff.val * scalar.val ∧
        product.val ≤ cap ∧
        newSum.val = oldSum.val + product.val ∧
        ∃ updated : Array U64 8#usize,
          Array.update sums limb newSum = .ok updated ∧ sums' = updated := by
  unfold InnerBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some limb =>
      obtain ⟨coeff, hcoeffRead, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨coeff64, hcoeffCast, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨scalar64, hscalarCast, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨product, hmul, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨oldSum, hsumRead, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨newSum, hadd, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨updated, hupdate, hfinal⟩ := bind_success _ _ _ hrest
      have hlimb : limb.val < 8 := by
        have hi := index_success_bound coefficient limb coeff hcoeffRead
        simpa [coefficient.property] using hi
      have hcoeffVal : coeff.val < 2147483647 := by
        have hi : limb.val < 8 := hlimb
        have hget : coeff = coefficient.val[limb.val]'(by simpa [coefficient.property] using hi) := by
          have hidx : limb.val < coefficient.length := by simpa using hi
          obtain ⟨x, hspec, hx⟩ := WP.spec_imp_exists (Array.index_usize_spec coefficient limb hidx)
          have hcx : coeff = x := Result.ok.inj (hcoeffRead.symm.trans hspec)
          exact hcx.trans hx
        rw [hget]
        exact hcoeff ⟨limb.val, by simpa using hi⟩
      have hsumVal : oldSum.val ≤ 3 * cap := by
        have hget : oldSum = sums.val[limb.val]'(by simpa [sums.property] using hlimb) := by
          have hidx : limb.val < sums.length := by simpa using hlimb
          obtain ⟨x, hspec, hx⟩ := WP.spec_imp_exists (Array.index_usize_spec sums limb hidx)
          have hcx : oldSum = x := Result.ok.inj (hsumRead.symm.trans hspec)
          exact hcx.trans hx
        have hbound := hprefix ⟨limb.val, by simpa using hlimb⟩
        simpa [hget] using hbound
      have hmulBound :
          (core.convert.num.FromU64U32.from coeff).val *
            (core.convert.num.FromU64U32.from scalar).val < 2^64 := by
        rw [widen_u32_value, widen_u32_value]
        have hcm : coeff.val < 2^31 := by omega
        have hsm : scalar.val < 2^31 := by omega
        have hprod := Nat.mul_lt_mul_of_lt_of_lt hcm hsm
        norm_num at hprod
        omega
      obtain ⟨productExpected, hmulExpected, hproductValue⟩ :=
        AspisR1.ExtractedCurrentReducerOps.mul_success
          (core.convert.num.FromU64U32.from coeff)
          (core.convert.num.FromU64U32.from scalar) hmulBound
      have hcoeff64Value : coeff64 = core.convert.num.FromU64U32.from coeff :=
        Result.ok.inj hcoeffCast.symm
      have hscalar64Value : scalar64 = core.convert.num.FromU64U32.from scalar :=
        Result.ok.inj hscalarCast.symm
      have hmul64 : UScalar.mul coeff64 scalar64 = .ok product := by
        change UScalar.mul coeff64 scalar64 = .ok product at hmul
        exact hmul
      have hmulTyped : UScalar.mul (core.convert.num.FromU64U32.from coeff)
          (core.convert.num.FromU64U32.from scalar) = .ok product := by
        rw [← hcoeff64Value, ← hscalar64Value]
        exact hmul64
      have hprodEq : product = productExpected := Result.ok.inj (hmulTyped.symm.trans hmulExpected)
      have hproductValue' : product.val = coeff.val * scalar.val := by
        calc
          product.val = productExpected.val := by rw [hprodEq]
          _ = (core.convert.num.FromU64U32.from coeff).val *
              (core.convert.num.FromU64U32.from scalar).val := hproductValue
          _ = coeff.val * scalar.val := by rw [widen_u32_value, widen_u32_value]
      have hproductBound : product.val ≤ cap := by
        rw [hproductValue']
        have hc : coeff.val ≤ 2147483646 := by omega
        have hs : scalar.val ≤ 2147483646 := by omega
        nlinarith [Nat.mul_le_mul hc hs]
      have hsumBound : oldSum.val + product.val < 2^64 := by
        have hcap : 4 * cap < 2^64 := by norm_num [cap]
        have hprev : oldSum.val ≤ 3 * cap := hsumVal
        omega
      obtain ⟨newExpected, haddExpected, hnewValue⟩ :=
        AspisR1.ExtractedCurrentReducerOps.add_success oldSum product hsumBound
      have haddTyped : UScalar.add oldSum product = .ok newSum := by
        change UScalar.add oldSum product = .ok newSum at hadd
        exact hadd
      have hnewEq : newSum = newExpected := Result.ok.inj (haddTyped.symm.trans haddExpected)
      have hnewValue' : newSum.val = oldSum.val + product.val := by
        calc
          newSum.val = newExpected.val := by rw [hnewEq]
          _ = oldSum.val + product.val := hnewValue
      have hsumEq : sums' = updated := by
        cases ControlFlow.cont.inj (Result.ok.inj hfinal)
        rfl
      refine ⟨limb, coeff, oldSum, product, newSum,
        hcoeffRead, hsumRead, hmulTyped, haddTyped,
        hproductValue', hproductBound, hnewValue', updated,
        hupdate, hsumEq⟩

#print axioms inner_body_success_arithmetic_update
end AspisR1FastDotsActualLimbArithmeticStepV2
