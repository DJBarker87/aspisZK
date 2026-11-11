import RPv_FJa_Expansion
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_Seed
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
/-- Original zero array and original one write; no assumed initial tensor. -/
theorem value {N : Usize} (seed : Array NQ N)
    (run : Array.update (Array.repeat N field.QM31.ZERO) 0#usize field.QM31.ONE=ok seed) :
    FIw_ArrayValue.canonical seed ∧ FIv_NativeArray.value seed 0=1 := by
  have cz : FIw_ArrayValue.canonical (Array.repeat N field.QM31.ZERO) := by
    intro x hx
    rw [(List.mem_replicate.mp hx).2]
    exact FIv_NativeValue.zero.1
  refine ⟨FJa_ArrayUpdate.canonical_write _ seed 0#usize _ cz FIv_NativeValue.one.1 run,?_⟩
  rw [FJa_ArrayUpdate.value _ seed 0#usize _ run 0]
  exact FIv_NativeValue.one.2
#print axioms value
end AspisR1.FJa_Seed
end
