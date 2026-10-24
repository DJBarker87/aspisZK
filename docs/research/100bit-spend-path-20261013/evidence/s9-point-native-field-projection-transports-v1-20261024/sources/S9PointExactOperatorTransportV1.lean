import S9SharedHighConstructorModelV1
import S9TwoFoldProductModelV1
import S9SymbolicRowTransportV1
import S9SourceFactorShapeTransportV1
import S9SourceQuarterModelBridgeV1
import S9OpaqueQEmbedTripleV1
import S9WideFieldOperatorBridgesV1
import S9PointNativeMulProjectionV1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit false
open scoped BigOperators
namespace AspisR1S9PointExactOperatorTransportV1
open AspisR1S9QuadraticFieldMulProjectionV1 (projectedMul)
open AspisR1S9PointNativeMulProjectionV1 (native_mul_projected)
abbrev E := AspisWideTower.WideExact
noncomputable def fieldTriple {K : Type} [Field K] (x y z : K) : K := (x*y)*z
noncomputable def fieldSum {I K : Type} [Field K] (s : Finset I) (f : I → K) : K := ∑ i ∈ s,f i
/-- Only opaque operands; no rows, byte reads or numeric field values. -/
theorem triple_operator_eq (x y z : E) : (x*y)*z=fieldTriple x y z := by
  have ho := native_mul_projected (x*y) z
  have hi := congrArg (fun a : E => projectedMul a z) (native_mul_projected x y)
  exact ho.trans hi
/-- The index type, finite set and summand are ALL opaque. No concrete
finite set is instantiated or enumerated in this operator interface. -/
theorem sum_operator_eq {I : Type} (s : Finset I) (f : I → E) :
    (∑ i ∈ s,f i)=fieldSum s f := by rfl
noncomputable def fieldScaledSum {I K : Type} [Fintype I] [Field K]
    (s : K) (f c : I → K) : K := s*∑ i,f i*c i

theorem scaled_sum_operator_eq {I : Type} [Fintype I] (s : E) (f c : I → E) :
    s*∑ i,f i*c i=fieldScaledSum s f c := by
  have hp : (fun i => f i*c i)=(fun i => projectedMul (f i) (c i)) :=
    funext (fun i => native_mul_projected (f i) (c i))
  have hs := sum_operator_eq Finset.univ (fun i => f i*c i)
  have hm := native_mul_projected s (∑ i,f i*c i)
  exact hm.trans (congrArg (projectedMul s)
    (hs.trans (congrArg (fieldSum Finset.univ) hp)))
#print axioms scaled_sum_operator_eq
#print axioms triple_operator_eq
#print axioms sum_operator_eq
end AspisR1S9PointExactOperatorTransportV1
