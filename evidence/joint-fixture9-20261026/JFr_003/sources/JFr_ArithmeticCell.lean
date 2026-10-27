import JFv_RawExtractedSemanticCallOpsV23
set_option autoImplicit false
namespace AspisR1.JFr_ArithmeticCell
open Aeneas Aeneas.Std Result
abbrev Q := AspisR1SemanticCallExtraction.aspis_core.field.QM31
def q (a b c d : U32) : Q := ⟨⟨a,b⟩,⟨c,d⟩⟩
theorem add : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add
    (q 73778079#u32 1547969474#u32 1813495781#u32 1947321224#u32)
    (q 1043776513#u32 1161764315#u32 2088723454#u32 1016233752#u32) =
    ok (q 1117554592#u32 562250142#u32 1754735588#u32 816071329#u32) := by rfl
#print axioms add
#print AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop.body
#print AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop.body
end AspisR1.JFr_ArithmeticCell
