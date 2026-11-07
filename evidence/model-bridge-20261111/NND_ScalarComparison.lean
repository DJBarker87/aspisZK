import NND_ScalarLaws
set_option autoImplicit false
namespace NND_Carrier
open Aeneas Aeneas.Std

theorem slot_injective : Function.Injective slot := by
 intro x y h
 exact (slot_back x).symm.trans ((congrArg unslot h).trans (slot_back y))

theorem byte_beq (x y : U8) : (byte x == byte y) = (x == y) := by
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq]
 exact ⟨fun h => byte_injective h, congrArg byte⟩

theorem slot_beq (x y : U64) : (slot x == slot y) = decide (x = y) := by
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq,decide_eq_true_eq]
 exact ⟨fun h => slot_injective h, congrArg slot⟩

theorem flags (x mask : U8) : (x &&& mask != 0#u8) = (byte x &&& byte mask != (0 : UInt8)) := by
 rw [← byte_and, ← byte_zero]
 simp only [bne,byte_beq]

#print axioms slot_injective
#print axioms byte_beq
#print axioms slot_beq
#print axioms flags
end NND_Carrier
