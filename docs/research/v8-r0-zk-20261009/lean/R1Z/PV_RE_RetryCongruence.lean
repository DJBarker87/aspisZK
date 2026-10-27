import R1Z.PV_RE_RetryStep
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_RetryCongruence
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]

/-- The recursive continuation is consulted only at the incremented counter,
and only after rejection. All entropy and attempt outcomes are retained. -/
theorem congr_at {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) (k j : Usize)
    (f g : Store → C → Usize → Reply)
    (inc : Aeneas.Std.lift (Usize.wrapping_add k 1#usize) = Result.ok j)
    (next : ∀ s c, f s c j = g s c j) :
    step entropy f pub compiled v hash store state k =
      step entropy g pub compiled v hash store state k := by
  unfold step
  split
  · rfl
  · congr 1
    funext x
    rcases x with ⟨r, c⟩
    cases r with
    | Err e => rfl
    | Ok secret =>
      change (prover.prove_masked_attempt pub compiled v hash secret store >>= _) =
        (prover.prove_masked_attempt pub compiled v hash secret store >>= _)
      congr 1
      funext y
      rcases y with ⟨r, s⟩
      cases r with
      | Ok proof => rfl
      | Err e =>
        cases e <;> try rfl
        rw [inc]
        exact next s c

#print axioms congr_at
end R1Z.PV_RE_RetryCongruence
