import NJA_CohortArity
import NJA_Context

set_option autoImplicit false
namespace NJE_ReadPackets
open Aeneas Aeneas.Std Result NJA_Multiproof

theorem TX1_121 (a : Array U32 16#usize) (i : Usize) :
    multiproof.index_at a i = AspisR1Stage2.multiproof.index_at a i ∧
    multiproof.index_at a i = Array.index_usize a i :=
  ⟨NJA_CohortArity.index a i, NJA_Arity.index_result a i⟩

theorem TX2_087 (a : Array U32 16#usize) (i : Usize) :
    multiproof.index_at a i = AspisR1Stage2.multiproof.index_at a i ∧
    multiproof.index_at a i = Array.index_usize a i := TX1_121 a i

-- Complete fail/ok source equation; native packet covers i<16.
-- Eight-branch reachability is listed separately, never silently pruned.
theorem TX1_126 (a : Array (Array U8 32#usize) 16#usize) (i : Usize) :
    multiproof.value_at a i = AspisR1Stage2.multiproof.value_at a i ∧
    multiproof.value_at a i = Array.index_usize a i :=
  ⟨NJA_CohortArity.value a i, NJA_Arity.value_result a i⟩

theorem TX2_092 (a : Array (Array U8 32#usize) 16#usize) (i : Usize) :
    multiproof.value_at a i = AspisR1Stage2.multiproof.value_at a i ∧
    multiproof.value_at a i = Array.index_usize a i := TX1_126 a i

#print TX1_121
#print axioms TX1_121
#print TX2_087
#print axioms TX2_087
#print TX1_126
#print axioms TX1_126
#print TX2_092
#print axioms TX2_092
end NJE_ReadPackets
