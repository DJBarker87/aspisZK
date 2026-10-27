import Aeneas
open Aeneas Aeneas.Std
namespace R1Z.PV_AL_ShiftLiterals
set_option autoImplicit false

/-- The Rust binary shifts in this emission have positive, in-range literal
counts. The current library's wrapping-shift API takes those counts as U32. -/
theorem shr31 (x : U64) :
    (⟨x.bv.ushiftRight 31⟩ : U64)=U64.wrapping_shr x 31#u32 := rfl

theorem shl32 (x : U64) :
    (⟨x.bv.shiftLeft 32⟩ : U64)=U64.wrapping_shl x 32#u32 := rfl

#print axioms shr31
#print axioms shl32
end R1Z.PV_AL_ShiftLiterals
