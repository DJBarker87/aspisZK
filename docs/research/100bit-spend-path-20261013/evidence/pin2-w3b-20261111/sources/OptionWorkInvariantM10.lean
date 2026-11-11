import PublicParserWork

set_option autoImplicit false
namespace AspisR1.OptionWorkInvariantM10

theorem bind_property {A B : Type} (x : Option A × Nat) (f : A → Option B × Nat)
    (P : Option B → Prop) (hn : P none)
    (hf : ∀ a, x.1 = some a → P (f a).1) : P (PublicParserWork.bind x f).1 := by
  unfold PublicParserWork.bind
  split
  · exact hn
  · rename_i a ha
    exact hf a ha

#print axioms bind_property
end AspisR1.OptionWorkInvariantM10
