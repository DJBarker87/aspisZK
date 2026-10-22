import FourDotsActualInnerLoopLinearBoundV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsHeadLimbForwardRootV1
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (InnerBody Range cap cell)
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev M31 := AspisR1FastDotsCurrent.aspis_core.field.M31

theorem widen_u32_value (x : Std.U32) :
    (core.convert.num.FromU64U32.from x).val=x.val := by
  change (x.bv.setWidth 64).toNat=x.bv.toNat
  apply BitVec.toNat_setWidth_of_le
  decide

/-- Canonical source operands and the current batch bound construct the
actual generated multiply/add/update step, without assuming body success. -/
theorem inner_body_forward
    (ops : Ops) (coefficient : Array Std.U32 8#usize)
    (iter iter' : Range) (limb : Usize) (sums : Array Std.U64 8#usize) (scalar : M31)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some limb,iter'))
    (hi : limb.val < 8)
    (hcoeff : ∀ j : Fin 8,
      (coefficient.val[j.val]'(by simpa [coefficient.property] using j.isLt)).val < 2147483647)
    (hcurrent : cell sums ⟨limb.val,hi⟩ ≤ 3*cap)
    (hscalar : scalar.val < 2147483647) :
    ∃ updated : Array Std.U64 8#usize,
      InnerBody ops coefficient iter sums scalar = .ok (.cont (iter',updated,scalar)) := by
  have hic : limb.val < coefficient.length := by simpa [Array.length,coefficient.property] using hi
  have his : limb.val < sums.length := by simpa [Array.length,sums.property] using hi
  obtain ⟨coeff,hcread,hcval⟩ := WP.spec_imp_exists (Array.index_usize_spec coefficient limb hic)
  obtain ⟨oldSum,hsread,hsval⟩ := WP.spec_imp_exists (Array.index_usize_spec sums limb his)
  have hc : coeff.val < 2147483647 := by
    rw [hcval]
    exact hcoeff ⟨limb.val,hi⟩
  have hs : oldSum.val ≤ 3*cap := by
    rw [hsval]
    exact hcurrent
  have hmulBound : (core.convert.num.FromU64U32.from coeff).val *
      (core.convert.num.FromU64U32.from scalar).val < 2^64 := by
    rw [widen_u32_value,widen_u32_value]
    have hprod := Nat.mul_lt_mul_of_lt_of_lt (show coeff.val < 2^31 by omega)
      (show scalar.val < 2^31 by omega)
    norm_num at hprod
    omega
  obtain ⟨product,hmul,hprodValue⟩ := AspisR1.ExtractedCurrentReducerOps.mul_success
    (core.convert.num.FromU64U32.from coeff) (core.convert.num.FromU64U32.from scalar) hmulBound
  have hp : product.val ≤ cap := by
    rw [hprodValue,widen_u32_value,widen_u32_value]
    have hc' : coeff.val ≤ 2147483646 := by omega
    have hs' : scalar.val ≤ 2147483646 := by omega
    simpa only [cap,pow_two] using Nat.mul_le_mul hc' hs'
  have hsumBound : oldSum.val+product.val < 2^64 := by
    have hcap : 4*cap < 2^64 := by norm_num [cap]
    omega
  obtain ⟨newSum,hadd,_hnewValue⟩ := AspisR1.ExtractedCurrentReducerOps.add_success oldSum product hsumBound
  obtain ⟨updated,hupdate,_hset⟩ := WP.spec_imp_exists (Array.update_spec sums limb newSum his)
  have hcastCoeff : (lift (core.convert.num.FromU64U32.from coeff) : Result Std.U64) =
      .ok (core.convert.num.FromU64U32.from coeff) := rfl
  have hcastScalar : (lift (core.convert.num.FromU64U32.from scalar) : Result Std.U64) =
      .ok (core.convert.num.FromU64U32.from scalar) := rfl
  have hmulTyped : ((core.convert.num.FromU64U32.from coeff) *
      (core.convert.num.FromU64U32.from scalar) : Result Std.U64) = .ok product := by
    change UScalar.mul _ _ = .ok product
    exact hmul
  have haddTyped : (oldSum + product : Result Std.U64) = .ok newSum := by
    change UScalar.add _ _ = .ok newSum
    exact hadd
  refine ⟨updated,?_⟩
  simp [InnerBody,
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0.body,
    hnext,hcread,hsread,hcastCoeff,hcastScalar,hmulTyped,haddTyped,hupdate]

/-- Construct the actual successful step first, then reuse the retained
phase-sensitive bound theorem on that exact returned array. -/
theorem inner_body_forward_linear_step
    (ops : Ops) (k : Nat) (hk : k ≤ 3)
    (coefficient : Array Std.U32 8#usize) (iter iter' : Range)
    (sums : Array Std.U64 8#usize) (scalar : M31)
    (hi : iter.start.val < 8)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some iter.start,iter'))
    (hcoeff : ∀ j : Fin 8,
      (coefficient.val[j.val]'(by simpa [coefficient.property] using j.isLt)).val < 2147483647)
    (hbase : ∀ j : Fin 8, cell sums j ≤ (k+1)*cap)
    (hsuffix : ∀ j : Fin 8, iter.start.val ≤ j.val → cell sums j ≤ k*cap)
    (hscalar : scalar.val < 2147483647) :
    ∃ updated : Array Std.U64 8#usize,
      InnerBody ops coefficient iter sums scalar = .ok (.cont (iter',updated,scalar)) ∧
      iter'.start.val=iter.start.val+1 ∧ iter'.end=iter.end ∧
      (∀ j : Fin 8, iter'.start.val ≤ j.val → cell updated j ≤ k*cap) ∧
      (∀ j : Fin 8, cell updated j ≤ (k+1)*cap) := by
  have hcurrent : cell sums ⟨iter.start.val,hi⟩ ≤ 3*cap := by
    exact le_trans (hsuffix ⟨iter.start.val,hi⟩ (Nat.le_refl _))
      (Nat.mul_le_mul_right cap hk)
  obtain ⟨updated,hbody⟩ := inner_body_forward ops coefficient iter iter' iter.start sums scalar
    hnext hi hcoeff hcurrent hscalar
  have hpost := AspisR1FastDotsActualInnerLoopLinearBoundV1.inner_body_success_linear_step
    ops k hk coefficient iter iter' sums updated scalar scalar hcoeff hbase hsuffix hscalar hbody
  exact ⟨updated,hbody,hpost⟩

#print axioms widen_u32_value
#print axioms inner_body_forward
#print axioms inner_body_forward_linear_step
end AspisR1FastDotsHeadLimbForwardRootV1
