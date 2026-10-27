import RPu_FIv_Arithmetic
set_option autoImplicit false
namespace AspisR1.FJb_PairProjection
/-- Symbolic tuple elimination as projections,for composing native mutable
array continuations without reducing their calls. -/
theorem value {A B C : Type} (p : A×B) (f : A → B → C) :
    Prod.casesOn p f=f p.1 p.2 := by
  rcases p with ⟨a,b⟩
  rfl
#print axioms value
end AspisR1.FJb_PairProjection
