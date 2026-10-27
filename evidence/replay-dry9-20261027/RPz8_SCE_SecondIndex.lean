import RPz8_SCE_Experiment
set_option autoImplicit false
namespace AspisR1.SCE_SecondIndex
open Aeneas Aeneas.Std Result S2W_D189Entry
/-- Literal runtime account positions, with all buffer contents opaque. -/
theorem proof0 (e : Entry) (sizes : Nat → Nat × Nat) :
    Slice.index_usize (e.second sizes) 0#usize = ok (e.snapshot 0 (sizes 0).1 (sizes 0).2) := rfl

theorem checkpoint6 (e : Entry) (sizes : Nat → Nat × Nat) :
    Slice.index_usize (e.second sizes) 6#usize = ok (e.snapshot 6 (sizes 6).1 (sizes 6).2) := rfl
#print axioms proof0
#print axioms checkpoint6
end AspisR1.SCE_SecondIndex
