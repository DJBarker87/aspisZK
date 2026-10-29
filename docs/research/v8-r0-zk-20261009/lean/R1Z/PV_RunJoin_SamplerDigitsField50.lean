import R1Z.PV_RunJoin_SamplerRaw49
import R0C.ModuloField
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SamplerDigitsField50
open Aeneas Aeneas.Std
open ProverCommitWideOps48
open PV_B2_C_ArrayDigits (limb)

def digits (a : Array U32 8#usize) (h : PV_B2_C_ArrayDigits.canonical a) : Fin 8 → Fin AspisCircleGroupOrder.P :=
  fun i => ⟨(limb a i).val,h i⟩

theorem complete (a : Array U32 8#usize) (h : PV_B2_C_ArrayDigits.canonical a) :
    value (PV_RunJoin_SamplerRaw49.raw a)=R0C.ModuloField.digitsField (digits a h) := by
  rw [R0C.ModuloField.digitsField_apply]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> rfl
  · apply QuadraticAlgebra.ext <;> rfl
#print axioms digits
#print axioms complete
end R1Z.PV_RunJoin_SamplerDigitsField50
