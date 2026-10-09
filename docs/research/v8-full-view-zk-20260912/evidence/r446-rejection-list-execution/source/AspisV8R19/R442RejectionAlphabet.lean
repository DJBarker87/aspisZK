import AspisV8R19.R421UniformMasked31Block

set_option autoImplicit false
namespace AspisV8R19.R442RejectionAlphabet

def alphabetDecode (p : Nat) (w : Fin (p + 1)) : Option (Fin p) :=
  if h : w.val < p then some ⟨w.val, h⟩ else none

def alphabetEncode (p : Nat) : Option (Fin p) → Fin (p + 1)
  | none => ⟨p, by omega⟩
  | some a => a.castSucc

/-- The accepted alphabet has `p` values and one explicit rejection sentinel. -/
def alphabetEquiv (p : Nat) : Fin (p + 1) ≃ Option (Fin p) where
  toFun := alphabetDecode p
  invFun := alphabetEncode p
  left_inv w := by
    apply Fin.ext
    by_cases h : w.val < p
    · simp [alphabetDecode, alphabetEncode, h]
    · have hp : w.val = p := by omega
      simp [alphabetDecode, alphabetEncode, h, hp]
  right_inv o := by
    cases o with
    | none =>
        simp [alphabetDecode, alphabetEncode]
    | some a =>
        simp [alphabetDecode, alphabetEncode, a.isLt]

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
#print axioms firstAccepted_map

end AspisV8R19.R442RejectionAlphabet
