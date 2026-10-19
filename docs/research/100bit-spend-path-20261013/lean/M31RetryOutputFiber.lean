import M31AcceptFiber
import FSRetryOutputUniformity

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

abbrev Value := Fin P31

def decode31 (w : Word) : Option Value :=
  if h : mask31 w < P31 then some ⟨mask31 w, h⟩ else none

theorem decode31_eq_some_iff (w : Word) (r : Value) :
    decode31 w = some r ↔ mask31 w = r.val := by
  unfold decode31
  by_cases hlt : mask31 w < P31
  · simp only [dif_pos hlt, Option.some.injEq]
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      exact Fin.ext h
  · simp only [dif_neg hlt]
    constructor
    · intro h
      cases h
    · intro h
      exact (hlt (h ▸ r.isLt)).elim

noncomputable def acceptedSet (r : Value) : Finset Word :=
  Finset.univ.filter fun w => mask31 w = r.val

noncomputable def acceptedValueEquiv (r : Value) :
    valueFiber decode31 r ≃ acceptedSet r where
  toFun x := ⟨x.1, by
    simp only [acceptedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact decode31_eq_some_iff x.1 r |>.mp x.2⟩
  invFun x := ⟨x.1, by
    exact (decode31_eq_some_iff x.1 r).2 (Finset.mem_filter.mp x.2).2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem decode31_valueFiberCard (r : Value) : valueFiberCard decode31 r = 2 := by
  letI : Fintype (valueFiber decode31 r) := valueFiberFintype decode31 r
  have hcard := Fintype.card_congr (acceptedValueEquiv r)
  have haccepted : Fintype.card (acceptedSet r) = 2 := by
    rw [Fintype.card_coe]
    unfold acceptedSet
    exact accepted_fiber_card r
  calc
    valueFiberCard decode31 r = Fintype.card (acceptedSet r) := by
      simpa [valueFiberCard] using hcard
    _ = 2 := haccepted

theorem outputFiber_card_eq (a b : Value) :
    outputFiberCard decode31 a = outputFiberCard decode31 b := by
  by_cases hab : a = b
  · subst b
    rfl
  · apply outputFiber_card_eq_of_value_fiber_card decode31 a b hab
    rw [decode31_valueFiberCard a, decode31_valueFiberCard b]

#print axioms decode31_valueFiberCard
#print axioms outputFiber_card_eq

end M31RetryOutputFiber
