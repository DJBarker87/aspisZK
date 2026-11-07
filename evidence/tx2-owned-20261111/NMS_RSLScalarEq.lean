import NMS_RSLScalars
import NLM_ScalarLaws
set_option autoImplicit false
namespace NMS_RSLScalarEq
open Aeneas Aeneas.Std NMS_RSLScalars

theorem scalar_bne {ty : UScalarTy} (a b : UScalar ty) :
 (a != b) = decide (a.val ≠ b.val) := by
 by_cases same : a = b
 · subst b; simp
 · have distinct : a.val ≠ b.val := fun h => same (NLM_ScalarLaws.scalar_eq a b h)
   simp [same,distinct]

theorem key_neq (a b : Aeneas.Std.Array U8 32#usize) :
 decide (b32 a ≠ b32 b) = !(decide (a = b)) := by
 by_cases same : a = b
 · subst b; simp
 · have distinct : b32 a ≠ b32 b := fun h => same (b32_injective h)
   simp [same,distinct]

theorem checkpoint_value : (1768#usize).val = RSL.CHECKPOINT_BYTES := by
 change (1768#usize).val = 1768
 scalar_tac

#print axioms scalar_bne
#print axioms key_neq
#print axioms checkpoint_value
end NMS_RSLScalarEq
