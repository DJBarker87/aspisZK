import NMT_345Continuation
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
/-- One occurrence of the first source equality, carrying the parent intact. -/
def route10 {W : Type} (c : Calls) (s : Parent W)
 (yes no : Parent W → Result Ret) : Result Ret := do
 let b ← c.c1 core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,10#u8])
 if b then yes s else no s
/-- The actual first route call is exposed with its exact continuation;
the admitted body remains opaque to this one-step lemma. -/
theorem emitted_route10 {W : Type} (c : Calls) (s : Parent W) :
 emitted c s = route10 c s (admitted c) (fun s => do
  let b ← c.c1 core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,11#u8])
  if b then admitted c s else .ok (.Err .InvalidInstructionData)) := rfl
#print axioms emitted_route10
end NMT_345
