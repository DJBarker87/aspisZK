import R1RawRoundCompletion

/-! Symbolic splitting and extensionality for raw round-record lists. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRecordSplit

open FS FS2 FS2.Duplex
open AspisV8R19.SourceDuplexStep
open AspisR1.InitialWalk

variable {M : Type}

theorem recs_split (s b : Nat → State) (m : Nat → M) (next : Nat → State)
    (n k : Nat) :
    RawRoundCompletion.recs s b m next (n + k) =
      RawRoundCompletion.recs s b m next n ++
        RawRoundCompletion.recs (fun j => s (n + j)) (fun j => b (n + j))
          (fun j => m (n + j)) (fun j => next (n + j)) k := by
  induction k with
  | zero => simp [RawRoundCompletion.recs]
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega]
      rw [RawRoundCompletion.recs_succ]
      rw [ih]
      rw [RawRoundCompletion.recs_succ
        (fun j => s (n + j)) (fun j => b (n + j))
        (fun j => m (n + j)) (fun j => next (n + j)) k]
      simp only [Function.comp_apply, Nat.add_assoc]
      simp only [List.append_assoc]

theorem recs_congr (s b : Nat → State) (m : Nat → M) (next : Nat → State)
    (s' b' : Nat → State) (m' : Nat → M) (next' : Nat → State) :
    ∀ n, (∀ j < n,
      s j = s' j ∧ b j = b' j ∧ m j = m' j ∧ next j = next' j) →
      RawRoundCompletion.recs s b m next n =
        RawRoundCompletion.recs s' b' m' next' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      rw [RawRoundCompletion.recs_succ, RawRoundCompletion.recs_succ]
      have hprefix : ∀ j < n,
          s j = s' j ∧ b j = b' j ∧ m j = m' j ∧ next j = next' j := by
        intro j hj
        exact h j (by omega)
      rw [ih hprefix]
      obtain ⟨hs, hb, hm, hnext⟩ := h n (by omega)
      simp [hs, hb, hm, hnext]

#print axioms recs_split
#print axioms recs_congr

end AspisR1.RawRecordSplit
end
