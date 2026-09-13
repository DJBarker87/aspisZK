import Mathlib.Logic.Equiv.Sum

/-! Common source decoding failures need not be discarded: an exact
success-domain permutation extends by the identity on all failed tapes. -/
set_option autoImplicit false
namespace AspisV8R13
variable {Failed Success : Type*}

def withFailureIdentity (e : Success ≃ Success) :
    (Failed ⊕ Success) ≃ (Failed ⊕ Success) := Equiv.sumCongr (Equiv.refl Failed) e

@[simp] theorem withFailureIdentity_failed (e : Success ≃ Success) (x : Failed) :
    withFailureIdentity e (Sum.inl x) = Sum.inl x := rfl

@[simp] theorem withFailureIdentity_succeeds (e : Success ≃ Success) (x : Success) :
    withFailureIdentity e (Sum.inr (α := Failed) x) =
      Sum.inr (α := Failed) (e x) := rfl

#print axioms withFailureIdentity_failed
end AspisV8R13
