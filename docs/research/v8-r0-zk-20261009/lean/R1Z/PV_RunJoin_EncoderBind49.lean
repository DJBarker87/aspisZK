import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderBind49
open Aeneas Aeneas.Std Result
theorem destructure {A B C : Type} (r : Result (A×B)) (k : A → B → Result C) :
    (do let (a,b) ← r;k a b)=(do let p ← r;k p.1 p.2) := by
  apply congrArg (Aeneas.Std.bind r)
  funext p
  rcases p with ⟨a,b⟩
  rfl
#print axioms destructure
end R1Z.PV_RunJoin_EncoderBind49
