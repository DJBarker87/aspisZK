import FIv_Arithmetic
set_option autoImplicit false
namespace AspisR1.FJb_PairBind
open Aeneas.Std Result
/-- Move a bind across a typed tuple elimination without evaluating its body. -/
theorem value {A B C D : Type} (p : A×B) (f : A → B → Result C) (k : C → Result D) :
    (do let v ← (let (a,b) := p;f a b);k v)=
      (let (a,b) := p;do let v ← f a b;k v) := by
  rcases p with ⟨a,b⟩
  rfl
#print axioms value
end AspisR1.FJb_PairBind
