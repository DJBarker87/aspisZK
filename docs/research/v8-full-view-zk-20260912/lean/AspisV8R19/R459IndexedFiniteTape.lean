import AspisV8R19.R456IndexedWordPermutation
import AspisV8R19.R443BoundedRejectionMass

set_option autoImplicit false
namespace AspisV8R19.R459IndexedFiniteTape

open AspisV8R19.R443BoundedRejectionMass

/-- Lift the accepted-coordinate-indexed word transform to a finite tape. -/
def transformTape {p : Nat} (σ : Nat → Equiv.Perm (Fin p)) (offset : Nat) :
    (n : Nat) → Tape p n → Tape p n
  | 0, t => t
  | n + 1, t =>
      match t 0 with
      | none => Fin.cases none (transformTape σ offset n (fun j => t j.succ))
      | some a => Fin.cases (some (σ offset a))
          (transformTape σ (offset + 1) n (fun j => t j.succ))

theorem transformTape_inverse_left {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset n : Nat) (t : Tape p n) :
    transformTape (fun i => (σ i).symm) offset n
      (transformTape σ offset n t) = t := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · cases h : t 0 <;> simp [transformTape, h]
      · cases h : t 0 <;> simp [transformTape, h, ih]

theorem transformTape_inverse_right {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset n : Nat) (t : Tape p n) :
    transformTape σ offset n
      (transformTape (fun i => (σ i).symm) offset n t) = t := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · cases h : t 0 <;> simp [transformTape, h]
      · cases h : t 0 <;> simp [transformTape, h, ih]

def finiteTapeEquiv {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset n : Nat) : Tape p n ≃ Tape p n where
  toFun := transformTape σ offset n
  invFun := transformTape (fun i => (σ i).symm) offset n
  left_inv := transformTape_inverse_left σ offset n
  right_inv := transformTape_inverse_right σ offset n

theorem ofFn_transformTape {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset n : Nat) (t : Tape p n) :
    List.ofFn (transformTape σ offset n t) =
      AspisV8R19.R456IndexedWordPermutation.transform σ offset (List.ofFn t) := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      cases h : t 0 <;>
        simp [transformTape, h, AspisV8R19.R456IndexedWordPermutation.transform, ih]

#print axioms transformTape_inverse_left
#print axioms transformTape_inverse_right
#print axioms finiteTapeEquiv
#print axioms ofFn_transformTape

end AspisV8R19.R459IndexedFiniteTape
