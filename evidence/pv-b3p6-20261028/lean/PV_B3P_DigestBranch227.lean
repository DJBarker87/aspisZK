import PV_B3P_DigestAssoc227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem digest_if_bind {α β : Type} (condition : Prop) [Decidable condition]
    (yes no : Result α) (f : α → Result β) :
    (if condition then yes else no) >>= f =
      if condition then yes >>= f else no >>= f := by
  by_cases hc : condition <;> simp only [hc,↓reduceIte]

theorem digest_option_bind {α β γ : Type} (recipient : Option α)
    (absent : Result β) (present : α → Result β) (f : β → Result γ) :
    (match recipient with | none => absent | some value => present value) >>= f =
      match recipient with | none => absent >>= f | some value => present value >>= f := by
  cases recipient <;> rfl

#print axioms digest_if_bind
#print axioms digest_option_bind
end PV_B3P_Success227
