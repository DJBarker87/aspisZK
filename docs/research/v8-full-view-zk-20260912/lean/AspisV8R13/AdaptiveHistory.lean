import Mathlib.Data.Set.Basic

/-! First divergence needs an actual query to a changed cell. Cached queries
are recorded just like all other public queries; no new fresh coin is drawn. -/
set_option autoImplicit false
namespace AspisV8R13
variable {Key Digest : Type*}

abbrev PublicHistory (Key Digest : Type*) := List (Key × Digest)

def publicRun (H : Key → Digest)
    (policy : PublicHistory Key Digest → Option Key) :
    Nat → PublicHistory Key Digest → PublicHistory Key Digest
  | 0, h => h
  | n+1, h => match policy h with
    | none => h
    | some key => publicRun H policy n (h ++ [(key,H key)])

def avoids (H : Key → Digest)
    (policy : PublicHistory Key Digest → Option Key) (touched : Set Key) :
    Nat → PublicHistory Key Digest → Prop
  | 0, _ => True
  | n+1, h => match policy h with
    | none => True
    | some key => key ∉ touched ∧ avoids H policy touched n (h ++ [(key,H key)])

theorem publicRun_eq_off_support (H H' : Key → Digest)
    (policy : PublicHistory Key Digest → Option Key) (touched : Set Key)
    (agrees : ∀ key, key ∉ touched → H' key = H key)
    (n : Nat) (h : PublicHistory Key Digest)
    (safe : avoids H policy touched n h) :
    publicRun H' policy n h = publicRun H policy n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    cases hp : policy h with
    | none => simp [publicRun, hp]
    | some key =>
      have hs : key ∉ touched ∧ avoids H policy touched n (h ++ [(key,H key)]) := by
        simpa [avoids, hp] using safe
      simp only [publicRun, hp]
      rw [agrees key hs.1]
      exact ih _ hs.2

#print axioms publicRun_eq_off_support
end AspisV8R13
