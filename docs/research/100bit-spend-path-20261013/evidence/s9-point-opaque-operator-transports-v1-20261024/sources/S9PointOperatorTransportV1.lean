import S9WideFieldOperatorBridgesV1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit false
open scoped BigOperators
namespace AspisR1S9PointOperatorTransportV1
open AspisR1S9WideMulOperatorBridgeV1 (mul_operator_eq fieldMul)
abbrev E := AspisWideTower.WideExact
noncomputable def fieldTriple {K : Type} [Field K] (x y z : K) : K := (x*y)*z
noncomputable def fieldSum {I K : Type} [Field K] (s : Finset I) (f : I → K) : K := ∑ i ∈ s,f i
/-- Only opaque operands; no rows, byte reads or numeric field values. -/
theorem triple_operator_eq (x y z : E) : (x*y)*z=fieldTriple x y z := by
  have ho := mul_operator_eq (x*y) z
  have hi := congrArg (fun a : E => fieldMul a z) (mul_operator_eq x y)
  exact ho.trans hi
/-- The index type, finite set and summand are ALL opaque. No concrete
finite set is instantiated or enumerated in this operator interface. -/
theorem sum_operator_eq {I : Type} (s : Finset I) (f : I → E) :
    (∑ i ∈ s,f i)=fieldSum s f := by rfl
noncomputable def fieldScaledSum {I K : Type} [Fintype I] [Field K]
    (s : K) (f c : I → K) : K := s*∑ i,f i*c i

theorem scaled_sum_operator_eq {I : Type} [Fintype I] (s : E) (f c : I → E) :
    s*∑ i,f i*c i=fieldScaledSum s f c := by
  have hp : (fun i => f i*c i)=(fun i => fieldMul (f i) (c i)) :=
    funext (fun i => mul_operator_eq (f i) (c i))
  have hs := sum_operator_eq Finset.univ (fun i => f i*c i)
  have hm := mul_operator_eq s (∑ i,f i*c i)
  exact hm.trans (congrArg (fieldMul s)
    (hs.trans (congrArg (fieldSum Finset.univ) hp)))
#print axioms scaled_sum_operator_eq
#print axioms triple_operator_eq
#print axioms sum_operator_eq
end AspisR1S9PointOperatorTransportV1
