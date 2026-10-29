import NDN_Reference15.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDN_RequestTagFinding

def zeroTagHeader : Array U8 8#usize :=
 Array.make 8#usize [65#u8,83#u8,81#u8,56#u8,1#u8,0#u8,1#u8,0#u8]

theorem extracted_accepts_zero :
 NDN_Reference15.header_gate zeroTagHeader 320#usize=ok 0#u8 := rfl

-- The selected AdapterRw model does not export transition_kind. No substitute
-- helper is introduced: source tags 1/2 are audited in Rust and checked by the
-- retained native counterexample. Only the bad extraction's zero fact is Lean.
#print axioms extracted_accepts_zero
end NDN_RequestTagFinding
