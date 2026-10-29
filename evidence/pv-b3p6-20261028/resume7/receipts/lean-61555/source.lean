import PV_B3P_Success227
import PV_B3P_P227_02
import PV_B3P_P227_03c
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- Preserve the value of a pure lifted scalar operation when composing
bounds proofs. No unconstrained continuation argument replaces that value. -/
theorem lift_total {α β : Type} (value : α) (next : α → Result β)
    (h : Success (next value)) : Success (lift value >>= next) := h

theorem raw_limb_total (output : Usize) (a b c d : U64) (ho : output.val<4) :
    Success (reference_poseidon.raw_limb227 output a b c d) := by
  have hc : output.val=0 ∨ output.val=1 ∨ output.val=2 ∨ output.val=3 := by omega
  rcases hc with h | h | h | h <;>
    simp only [reference_poseidon.raw_limb227,h,lift,bind_tc_ok] <;> exact ok _

theorem modulus_total : Success reference_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND := by
  unfold reference_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND aspis_core.field.P
  exact ⟨_,rfl⟩

#print axioms modulus_total
#print axioms lift_total
#print axioms raw_limb_total
end PV_B3P_Success227
