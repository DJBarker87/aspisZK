import AspisV8R19.R442RejectionAlphabet

set_option autoImplicit false
namespace AspisV8R19.R443BoundedRejectionMass
open OracleResampling
noncomputable section

variable {p : Nat}

abbrev Tape (p n : Nat) := Fin n → Option (Fin p)

def splitTape (p n : Nat) : Tape p (n+1) ≃ (Option (Fin p) × Tape p n) where
  toFun t := (t 0, fun i => t i.succ)
  invFun q := Fin.cases q.1 q.2
  left_inv t := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv q := by
    apply Prod.ext
    · rfl
    · funext i; rfl

def run : (n : Nat) → Tape p n → Option (Fin p)
  | 0, _ => none
  | n+1, t => match t 0 with
    | none => run n (fun i => t i.succ)
    | some a => some a

theorem mean_option (f : Option (Fin p) → ℚ) :
    mean f = (f none + ∑ a : Fin p, f (some a)) / (p+1 : ℚ) := by
  simp [mean, Fintype.sum_option, Fintype.card_option]

theorem mean_step (n : Nat) (f : Option (Fin p) → ℚ) :
    mean (fun t : Tape p (n+1) => f (run (n+1) t)) =
      (mean (fun t : Tape p n => f (run n t)) + ∑ a : Fin p, f (some a)) /
        (p+1 : ℚ) := by
  let g : Option (Fin p) → ℚ := fun w => match w with
    | none => mean (fun t : Tape p n => f (run n t))
    | some a => f (some a)
  calc
    _ = mean (fun q : Option (Fin p) × Tape p n =>
          f (run (n+1) ((splitTape p n).symm q))) :=
      (mean_equiv (splitTape p n).symm
        (fun t : Tape p (n+1) => f (run (n+1) t))).symm
    _ = mean (fun w : Option (Fin p) => mean (fun t : Tape p n =>
          f (run (n+1) ((splitTape p n).symm (w,t))))) :=
      mean_prod (fun (w : Option (Fin p)) (t : Tape p n) =>
        f (run (n+1) ((splitTape p n).symm (w,t))))
    _ = mean g := by
      apply mean_congr
      intro w
      cases w with
      | none => rfl
      | some a => exact mean_const (f (some a))
    _ = _ := mean_option g

def failureMass (p n : Nat) : ℚ :=
  mean (fun t : Tape p n => if run n t = none then 1 else 0)

def valueMass (p n : Nat) (a : Fin p) : ℚ :=
  mean (fun t : Tape p n => if run n t = some a then 1 else 0)

theorem failure_mass (p n : Nat) :
    failureMass p n = (1 / (p+1 : ℚ)) ^ n := by
  induction n with
  | zero => simp [failureMass, run, mean_const]
  | succ n ih =>
    rw [failureMass, mean_step n (fun x => if x = none then (1 : ℚ) else 0)]
    simp only [Option.some_ne_none, ↓reduceIte, Finset.sum_const_zero, add_zero]
    change failureMass p n / (p+1 : ℚ) = _
    rw [ih, pow_succ]
    ring

theorem value_mass (p n : Nat) (a : Fin p) :
    valueMass p n a = (1 - (1 / (p+1 : ℚ)) ^ n) / p := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by have := a.isLt; omega)
  have hm : (p+1 : ℚ) ≠ 0 := by positivity
  induction n with
  | zero => simp [valueMass, run, mean_const]
  | succ n ih =>
    rw [valueMass, mean_step n (fun x => if x = some a then (1 : ℚ) else 0)]
    simp only [Option.some.injEq]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    change (valueMass p n a + 1) / (p+1 : ℚ) = _
    rw [ih, pow_succ]
    field_simp
    ring

#print axioms mean_step
#print axioms failure_mass
#print axioms value_mass
end
end AspisV8R19.R443BoundedRejectionMass
