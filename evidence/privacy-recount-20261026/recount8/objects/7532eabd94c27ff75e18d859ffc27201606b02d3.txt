import R1Z.ProverCommitFuelJoin22
import R1Z.ProverCommitJointHistory19
/-! Product construction for rejection sampling. Swap a uniform nonzero model
coin with the first nonzero word of an independent raw tape. The swap is an
involution, so the entire reconstructed raw tape is exactly uniform, including
its rejected prefix and unused suffix. No shipped caller is postulated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitProduct25
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.LawTransport
open R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable
variable {A : Type} (zero : A)
abbrev NZ := {a : A // a ≠ zero}

def swap : (n : Nat) → NZ zero × (Fin n → A) → NZ zero × (Fin n → A)
  | 0, p => p
  | n+1, (coin,tape) =>
    if h : tape 0 = zero then
      let q := swap n (coin,fun i => tape i.succ)
      (q.1,Fin.cons zero q.2)
    else (⟨tape 0,h⟩,Fin.cons coin.val (fun i => tape i.succ))

theorem swap_involution (n : Nat) (p : NZ zero × (Fin n → A)) :
    swap zero n (swap zero n p) = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨coin,tape⟩
    by_cases h : tape 0 = zero
    · simp only [swap,h,dite_true,dite_false,Fin.cons_zero,Fin.cons_succ]
      rw [ih]
      congr 1
      funext i
      exact Fin.cases h.symm (fun _ => rfl) i
    · simp only [swap,h,dite_true,dite_false,Fin.cons_zero,Fin.cons_succ,coin.property]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

def swapEquiv (n : Nat) : (NZ zero × (Fin n → A)) ≃ (NZ zero × (Fin n → A)) where
  toFun := swap zero n
  invFun := swap zero n
  left_inv := swap_involution zero n
  right_inv := swap_involution zero n

/-- A complete tape, not only its next accepted answer, has the exact raw
uniform law. The independent model coin remains in the original product. -/
theorem raw_marginal [Fintype A] [Nonempty (NZ zero)] (n : Nat) :
    MP (fun p : NZ zero × (Fin n → A) => (swap zero n p).2) :=
  mp_comp (mp_equiv (swapEquiv zero n)) mp_snd

/-- The model projection has its original uniform nonzero law and ignores
all independent fuel words. -/
theorem model_marginal [Fintype A] [Nonempty A] (n : Nat) :
    MP (Prod.fst : NZ zero × (Fin n → A) → NZ zero) := mp_fst

def first : {n : Nat} → (Fin n → A) → Option A
  | 0, _ => none
  | _+1, tape => if tape 0 = zero then first (fun i => tape i.succ) else some (tape 0)

def exhausted {n : Nat} (tape : Fin n → A) : Prop := ∀ i, tape i = zero

/-- The reconstructed search returns the model coin unless the retained
independent tape is all zero. No success hypothesis is required. -/
theorem first_swap (n : Nat) (coin : NZ zero) (tape : Fin n → A) :
    first zero (swap zero n (coin,tape)).2 =
      if exhausted zero tape then none else some coin.val := by
  induction n with
  | zero => simp [first,exhausted]
  | succ n ih =>
    by_cases h : tape 0 = zero
    · have ex : exhausted zero tape ↔ exhausted zero (fun i => tape i.succ) := by
        constructor
        · intro hall i; exact hall i.succ
        · intro hall i; exact Fin.cases h hall i
      simp only [swap,h,dite_true,dite_false,first,Fin.cons_zero,Fin.cons_succ,if_pos rfl]
      rw [ih]
      simp only [ex,if_true]
    · have ex : ¬ exhausted zero tape := fun hall => h (hall 0)
      simp only [swap,h,dite_true,dite_false,first,Fin.cons_zero,coin.property,if_false,ex]

/-- Explicit product coupling: reconstructed raw tape versus the original
model coin and independent fuel tape, with both exact marginals. -/
def coupling [Fintype A] [Nonempty (NZ zero)] (n : Nat) :
    Coupling (Fin n → A) (NZ zero × (Fin n → A)) where
  S := NZ zero × (Fin n → A)
  finS := inferInstance
  nonemptyS := by
    letI : Nonempty A := ⟨(Classical.choice (inferInstance : Nonempty (NZ zero))).val⟩
    infer_instance
  toR := fun p => (swap zero n p).2
  toM := id
  meanR := raw_marginal zero n
  meanM := fun _ => rfl

/-- Twenty-four independent instances preserve the whole array of source
words, without enumerating the answer space or computing a recurrence. -/
theorem instances_marginal [Fintype A] [Nonempty A] [Nonempty (NZ zero)]
    (instances fuel : Nat) :
    MP (fun p : Fin instances → NZ zero × (Fin fuel → A) =>
      fun i => (swap zero fuel (p i)).2) := mp_pi (raw_marginal zero fuel) instances

#print axioms swap_involution
#print axioms raw_marginal
#print axioms model_marginal
#print axioms first_swap
#print axioms coupling
#print axioms instances_marginal
end R1Z.ProverCommitProduct25
