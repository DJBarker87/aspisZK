import AspisV8R19.R421UniformMasked31Block

set_option autoImplicit false
namespace AspisV8R19.R442RejectionAlphabet

/-- The accepted alphabet has `p` values and one explicit rejection sentinel. -/
def alphabetEquiv (p : Nat) : Fin (p + 1) ≃ Option (Fin p) where
  toFun w :=
    if h : w.val < p then some ⟨w.val, h⟩ else none
  invFun
    | none => ⟨p, by omega⟩
    | some a => a.castSucc
  left_inv w := by
    apply Fin.ext
    by_cases h : w.val < p
    · simp [h]
    · have hp : w.val = p := by omega
      simp [h, hp]
  right_inv o := by
    cases o with
    | none =>
        simp [alphabetEquiv]
    | some a =>
        simp [alphabetEquiv, a.isLt]

/-- Return the first accepted value, skipping rejection sentinels. -/
def firstAccepted {p : Nat} : List (Option (Fin p)) → Option (Fin p)
  | [] => none
  | none :: xs => firstAccepted xs
  | some a :: _ => some a

theorem firstAccepted_map {p : Nat} (σ : Equiv.Perm (Fin p))
    (xs : List (Option (Fin p))) :
    firstAccepted (xs.map (Option.map σ)) =
      Option.map σ (firstAccepted xs) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | none => exact ih
      | some a => rfl

#print axioms alphabetEquiv
#print axioms firstAccepted

end AspisV8R19.R442RejectionAlphabet
