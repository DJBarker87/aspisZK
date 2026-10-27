import R1Z.PV_Src_PortNodeCopy
set_option autoImplicit false
namespace R1Z.PV_Src_PortBindPair
open Aeneas Aeneas.Std Result
variable {A B C D : Type}

theorem source (x : Result (A × B)) (f : A → B → Result C) (g : C → Result D) :
    (do let c ← (do let (a,b) ← x;f a b);g c) =
    (do let (a,b) ← x;let c ← f a b;g c) := by
  cases x with
  | ok p => rcases p with ⟨a,b⟩;rfl
  | fail e => rfl
  | div => rfl

#print axioms source
end R1Z.PV_Src_PortBindPair
