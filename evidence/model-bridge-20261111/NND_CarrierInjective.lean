import NND_PoolArrays
set_option autoImplicit false
namespace NND_Carrier
open Aeneas Aeneas.Std
@[simp] theorem byte_eq_iff (x y : U8) : byte x = byte y ↔ x = y :=
 ⟨fun h => byte_injective h,congrArg byte⟩
@[simp] theorem word_eq_iff (x y : U32) : word x = word y ↔ x = y :=
 ⟨fun h => word_injective h,congrArg word⟩
@[simp] theorem slot_eq_iff (x y : U64) : slot x = slot y ↔ x = y :=
 ⟨fun h => slot_injective h,congrArg slot⟩
@[simp] theorem key_eq_iff (x y : Array U8 32#usize) : key x = key y ↔ x = y :=
 ⟨fun h => key_injective h,congrArg key⟩
@[simp] theorem digest_eq_iff (x y : Array U32 8#usize) : digest x = digest y ↔ x = y :=
 ⟨fun h => digest_injective h,congrArg digest⟩
@[simp] theorem frontier_eq_iff (x y : Array (Array U32 8#usize) 20#usize) : frontier x = frontier y ↔ x = y :=
 ⟨fun h => frontier_injective h,congrArg frontier⟩
@[simp] theorem slots_eq_iff (x y : Array U64 8#usize) : slots x = slots y ↔ x = y :=
 ⟨fun h => slots_injective h,congrArg slots⟩
#print axioms byte_eq_iff
#print axioms word_eq_iff
#print axioms slot_eq_iff
#print axioms key_eq_iff
#print axioms digest_eq_iff
#print axioms frontier_eq_iff
#print axioms slots_eq_iff
end NND_Carrier
