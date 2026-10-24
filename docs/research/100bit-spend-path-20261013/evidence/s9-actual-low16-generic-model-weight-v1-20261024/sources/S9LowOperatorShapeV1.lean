import S9WideFieldOperatorBridgesV1
import S9ActualLow16BodyMeaningV1
set_option autoImplicit false
noncomputable section
namespace AspisR1S9LowOperatorShapeV1
open AspisR1S9WideMulOperatorBridgeV1
open AspisR1S9WideFieldOperatorBridgesV1
abbrev E := AspisWideTower.WideExact

/-- Generic field expression; c remains opaque until the separate source
quarter theorem has been instantiated. -/
def lowWithQuarter {K : Type} [Field K] (a0 a1 c : K) (s : Fin 16) : K :=
  (a0^((4-s.val%4)%4)*a1^((4-s.val/4)%4))*c^2

theorem low_with_quarter_square {K : Type} [Field K] (a0 a1 c : K) (s : Fin 16) :
    lowWithQuarter a0 a1 c s=
      (a0^((4-s.val%4)%4)*a1^((4-s.val/4)%4))*(c*c) := by
  unfold lowWithQuarter
  rw [pow_two]

/-- Name the generic projected operations before specializing K. -/
theorem low_square_operator_api {K : Type} [Field K] (a0 a1 c : K) (s : Fin 16) :
    lowWithQuarter a0 a1 c s=
      fieldMul (fieldMul (fieldPow a0 ((4-s.val%4)%4))
        (fieldPow a1 ((4-s.val/4)%4))) (fieldMul c c) := by
  exact low_with_quarter_square a0 a1 c s

theorem source_permuted_index (n : Nat) (hn : n<4) :
    AspisR1S9ActualLow16BodyMeaningV1.permutedIndex n=(4-n)%4 := by
  have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
  rcases h with h|h|h|h <;> subst n <;> rfl

/-- Compare only symbolic operators; no E value, quarter or source powers
are normalized by the kernel. -/
theorem source_low_operator_shape (a0 a1 c : E) (s : Fin 16) :
    ((a0^AspisR1S9ActualLow16BodyMeaningV1.permutedIndex (s.val%4))*
      (a1^AspisR1S9ActualLow16BodyMeaningV1.permutedIndex (s.val/4)))*(c*c)=
      lowWithQuarter a0 a1 c s := by
  rw [source_permuted_index (s.val%4) (Nat.mod_lt _ (by decide)),
    source_permuted_index (s.val/4) (by have hs:=s.isLt;omega)]
  have hshape := low_square_operator_api (K:=E) a0 a1 c s
  conv_rhs => rw [hshape]
  change concreteMul (concreteMul (a0^((4-s.val%4)%4))
    (a1^((4-s.val/4)%4))) (concreteMul c c)=_
  rw [mul_operator_eq,mul_operator_eq,mul_operator_eq,
    pow_operator_eq,pow_operator_eq]

#print axioms low_with_quarter_square
#print axioms low_square_operator_api
#print axioms source_permuted_index
#print axioms source_low_operator_shape
end AspisR1S9LowOperatorShapeV1
end
