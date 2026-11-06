import NKR_SumRegroup
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumTensorAlgebra
open FIv_NativeValue (K)

/-- The two physical endpoint channels share the SAME coefficient basis.
This specializes sparse contraction to producer+consumer source136sums,
without evaluating any actual registry or recurrence. -/
theorem contraction_two {C P : Type} [Fintype C] [Fintype P] [DecidableEq P]
 (out0 out1 : C → P) (inside : P → Prop) [DecidablePred inside]
 (term : P → K) (value0 value1 : C → K) :
 (∑ p : P,if inside p then term p*(∑ c : C,
  ((if out0 c=p then value0 c else 0)+(if out1 c=p then value1 c else 0))) else 0)=
 ∑ c : C,((if inside (out0 c) then term (out0 c)*value0 c else 0)+
  (if inside (out1 c) then term (out1 c)*value1 c else 0)) := by
 calc
  _=(∑ p : P,if inside p then term p*(∑ c : C,if out0 c=p then value0 c else 0) else 0)+
    (∑ p : P,if inside p then term p*(∑ c : C,if out1 c=p then value1 c else 0) else 0) := by
   rw [←Finset.sum_add_distrib]
   apply Finset.sum_congr rfl
   intro p hp
   by_cases h : inside p <;> simp [h,Finset.sum_add_distrib,mul_add]
  _=_ := by
   rw [NKR_SumRegroup.contraction,NKR_SumRegroup.contraction,Finset.sum_add_distrib]

#print axioms contraction_two
end AspisR1.NKR_SumTensorAlgebra
end
